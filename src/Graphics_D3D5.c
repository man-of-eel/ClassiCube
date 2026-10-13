#include "ExtMath.h"
#include "Graphics.h"
#include "Logger.h"
#include "Platform.h"
#include "Window.h"

#if CC_GFX_BACKEND == CC_GFX_BACKEND_D3D5

#define CC_DYNAMIC_VBS_ARE_STATIC
#include "Errors.h"
#include "Menus.h"
#include "_GraphicsBase.h"

#define D3D_OVERLOADS
#define INITGUID
#define DIRECT3D_VERSION 0x0500
#include <d3d.h>
#include <ddraw.h>
#include <windows.h>

#define PACKED_TO_D3DCOLOR(pc) ((D3DCOLOR)(pc))

static void Gfx_RestoreState(void);
static void Gfx_FreeState(void);
static void D3D5_RestoreRenderStates(void);

static IDirectDraw2 *ddraw;
static IDirectDrawSurface *frontBuffer;
static IDirectDrawSurface *backBuffer;
static IDirectDrawSurface *zBuffer;
static IDirect3D2 *d3d;
static IDirect3DDevice2 *device;
static IDirect3DViewport2 *view;
static HWND hwnd;

static cc_bool WindowedMode;
static int cachedWidth, cachedHeight;
static int depthBits;
static DWORD deviceZBitDepths;
static cc_bool gfx_perspective, gfx_textureson, gfx_exclusive, gfx_forceload, useLoadPattern;
static int gfx_depth;
static cc_bool deviceIsSoftware;

static D3DMATRIX _view, _proj;

static void MatrixToD3D(D3DMATRIX* dst, const struct Matrix* src) {
	dst->_11 = src->row1.x; dst->_12 = src->row1.y; dst->_13 = src->row1.z; dst->_14 = src->row1.w;
	dst->_21 = src->row2.x; dst->_22 = src->row2.y; dst->_23 = src->row2.z; dst->_24 = src->row2.w;
	dst->_31 = src->row3.x; dst->_32 = src->row3.y; dst->_33 = src->row3.z; dst->_34 = src->row3.w;
	dst->_41 = src->row4.x; dst->_42 = src->row4.y; dst->_43 = src->row4.z; dst->_44 = src->row4.w;
}

struct ModeSearch { 
	int targetWidth, targetHeight, targetDepth;
	int bestWidth, bestHeight, bestDepth;
};

static void FatalError(HRESULT hr, const char *function) {
	Process_Abort2(hr, function);
}

static HRESULT CALLBACK EnumDeviceCallback(GUID FAR* lpGuid, LPSTR lpDeviceDescription, LPSTR lpDeviceName, LPD3DDEVICEDESC lpHWDesc, LPD3DDEVICEDESC lpHELDesc, LPVOID lpContext) {
	if (lpHWDesc->dwSize) {
		deviceZBitDepths |= lpHWDesc->dwDeviceZBufferBitDepth;
	}
	return D3DENUMRET_OK;
}

static HRESULT CALLBACK EnumModesCallback(LPDDSURFACEDESC desc, LPVOID context) {
	struct ModeSearch* search = (struct ModeSearch*)context;
	int bpp = desc->ddpfPixelFormat.dwRGBBitCount;
	if (bpp < 16) return DDENUMRET_OK; // Ignore 8bpp or lower

	if (desc->dwWidth == search->targetWidth && desc->dwHeight == search->targetHeight) {
		if (bpp == search->targetDepth) {
			search->bestWidth = desc->dwWidth;
			search->bestHeight = desc->dwHeight;
			search->bestDepth = bpp;
			return DDENUMRET_CANCEL; // Exact match found
		}

		if (search->bestWidth != search->targetWidth) {
			search->bestWidth = desc->dwWidth;
			search->bestHeight = desc->dwHeight;
			search->bestDepth = bpp;
		} else {
			// Prioritize 32 > 16 > 24
			if (bpp == 32) search->bestDepth = 32;
			else if (bpp == 16 && search->bestDepth != 32) search->bestDepth = 16;
		}
	}
	return DDENUMRET_OK;
}

static void Gfx_SetDisplayMode(void) {
	struct ModeSearch search;
	int w = Game.Width, h = Game.Height, d = DisplayInfo.Depth;
	Platform_Log3("Attempting SetDisplayMode %i %i %i", &w, &h, &d);

	search.targetWidth = w; search.targetHeight = h; search.targetDepth = d;
	search.bestWidth = -1; search.bestHeight = -1; search.bestDepth = -1;
	ddraw->lpVtbl->EnumDisplayModes(ddraw, 0, NULL, &search, EnumModesCallback);

	if (search.bestWidth == -1) {
		w = DisplayInfo.Width; h = DisplayInfo.Height;
		Platform_Log2("Requested mode not found, trying desktop %i x %i", &w, &h);
		search.targetWidth = w; search.targetHeight = h;
		ddraw->lpVtbl->EnumDisplayModes(ddraw, 0, NULL, &search, EnumModesCallback);
	}

	if (search.bestWidth == -1) {
		w = 640; h = 480;
		Platform_Log2("Desktop mode not found? trying %i x %i", &w, &h);
		search.targetWidth = w; search.targetHeight = h;
		ddraw->lpVtbl->EnumDisplayModes(ddraw, 0, NULL, &search, EnumModesCallback);
	}

	if (search.bestWidth == -1) FatalError(DDERR_INVALIDMODE, "No suitable fullscreen mode found");

	Platform_Log3("Final SetDisplayMode: %i %i %i", &search.bestWidth, &search.bestHeight, &search.bestDepth);
	HRESULT hr = ddraw->lpVtbl->SetDisplayMode(ddraw, search.bestWidth, search.bestHeight, search.bestDepth, 0, 0);
	if (FAILED(hr)) FatalError(hr, "SetDisplayMode");

	Game.Width   = search.bestWidth;
	Game.Height  = search.bestHeight;
	cachedWidth  = Game.Width;
	cachedHeight = Game.Height;
}

static void TryCreateDevice(void) {
	HRESULT hr = d3d->lpVtbl->CreateDevice(d3d, &IID_IDirect3DHALDevice, backBuffer, &device);
	if (FAILED(hr)) {
		Platform_Log1("could not create d3d hal device (%h), trying rgb device...", &hr);
		deviceIsSoftware = true;
		hr = d3d->lpVtbl->CreateDevice(d3d, &IID_IDirect3DRGBDevice, backBuffer, &device);
		if (FAILED(hr)) FatalError(hr, "CreateDevice");
	} else {
		deviceIsSoftware = false;
	}

	D3DDEVICEDESC hwDesc = { 0 }, swDesc = { 0 };
	hwDesc.dwSize = sizeof(D3DDEVICEDESC);
	swDesc.dwSize = sizeof(D3DDEVICEDESC);
	
	hr = device->lpVtbl->GetCaps(device, &hwDesc, &swDesc);
	if (SUCCEEDED(hr)) {
		D3DDEVICEDESC* caps = deviceIsSoftware ? &swDesc : &hwDesc;
		Platform_Log4("MaxTexWidth: %i, MaxTexHeight: %i, MinTexWidth: %i, MinTexHeight: %i", 
			&caps->dwMaxTextureWidth, &caps->dwMaxTextureHeight, &caps->dwMinTextureWidth, &caps->dwMinTextureHeight);
		Gfx.MaxTexWidth  = caps->dwMaxTextureWidth  ? caps->dwMaxTextureWidth  : Gfx.MaxTexWidth;
		Gfx.MaxTexHeight = caps->dwMaxTextureHeight ? caps->dwMaxTextureHeight : Gfx.MaxTexHeight;
		Gfx.MinTexWidth  = caps->dwMinTextureWidth  ? caps->dwMinTextureWidth  : Gfx.MinTexWidth;
		Gfx.MinTexHeight = caps->dwMinTextureHeight ? caps->dwMinTextureHeight : Gfx.MinTexHeight;

		DWORD texCaps = caps->dpcTriCaps.dwTextureCaps;
		if (!(texCaps & D3DPTEXTURECAPS_POW2)) {
			// this breaks some UI for some reason
			// Gfx.NonPowTwoTexturesSupport = GFX_NONPOW2_FULL;
		}
		
		if (texCaps & D3DPTEXTURECAPS_SQUAREONLY) {
			Platform_LogConst("Warning: GPU requires square textures");
		}
	} else {
		Platform_Log1("GetCaps failed: %h", &hr);
	}
}

/*########################################################################################################################*
 *------------------------------------------------------Initialization-----------------------------------------------------*
 *#########################################################################################################################*/
static GUID g_DeviceGUID;
static BOOL g_FoundSecondary = FALSE;

BOOL CALLBACK DDEnumCallback(GUID FAR* lpGUID, LPSTR lpDesc, LPSTR lpName, LPVOID lpContext) {
		if (lpGUID != NULL) {
				const char* desc = lpDesc ? lpDesc : "Unknown Device";
				Platform_Log1("Found Hardware: %c", desc);
				g_DeviceGUID = *lpGUID; 
				g_FoundSecondary = TRUE;
				return DDENUMRET_CANCEL; 
		}

		return DDENUMRET_OK;
}

 static DDSURFACEDESC GetSurfaceDesc(int width, int height, DWORD caps) {
	DDSURFACEDESC desc = {0};
	desc.dwSize = sizeof(DDSURFACEDESC);
	desc.dwFlags = DDSD_CAPS;
	desc.ddsCaps.dwCaps = caps;
	if (width > 0 && height > 0) {
		desc.dwFlags |= DDSD_WIDTH | DDSD_HEIGHT;
		desc.dwWidth = width;
		desc.dwHeight = height;
	}
	return desc;
}

static void CreateSurfaces(void) {
		HRESULT hr;
		DDSURFACEDESC desc = {0};
		desc.dwSize = sizeof(DDSURFACEDESC);

		if (!WindowedMode) {
				// --- FULLSCREEN MODE: Create a complex flipping chain ---
				desc.dwFlags = DDSD_CAPS | DDSD_BACKBUFFERCOUNT;
				desc.ddsCaps.dwCaps = DDSCAPS_PRIMARYSURFACE | DDSCAPS_FLIP | 
															DDSCAPS_COMPLEX | DDSCAPS_3DDEVICE;
				desc.dwBackBufferCount = 1;

				hr = ddraw->lpVtbl->CreateSurface(ddraw, &desc, &frontBuffer, NULL);
				if (FAILED(hr)) FatalError(hr, "CreateSurface(front) Fullscreen");

				// The back buffer is automatically created; we just have to "find" it
				DDSCAPS caps = { DDSCAPS_BACKBUFFER };
				hr = frontBuffer->lpVtbl->GetAttachedSurface(frontBuffer, &caps, &backBuffer);
				if (FAILED(hr)) FatalError(hr, "GetAttachedSurface(back)");

		} else {
				// --- WINDOWED MODE: Create independent surfaces ---
				// 1. Front Buffer (The Desktop)
				desc.dwFlags = DDSD_CAPS;
				desc.ddsCaps.dwCaps = DDSCAPS_PRIMARYSURFACE;
				hr = ddraw->lpVtbl->CreateSurface(ddraw, &desc, &frontBuffer, NULL);
				if (FAILED(hr)) FatalError(hr, "CreateSurface(front) Windowed");

				// 2. Back Buffer (Offscreen plain surface)
				DDSURFACEDESC backDesc = {0};
				backDesc.dwSize = sizeof(DDSURFACEDESC);
				backDesc.dwFlags = DDSD_CAPS | DDSD_WIDTH | DDSD_HEIGHT;
				backDesc.ddsCaps.dwCaps = DDSCAPS_OFFSCREENPLAIN | DDSCAPS_3DDEVICE;
				backDesc.dwWidth  = Game.Width;
				backDesc.dwHeight = Game.Height;
				
				hr = ddraw->lpVtbl->CreateSurface(ddraw, &backDesc, &backBuffer, NULL);
				if (FAILED(hr)) FatalError(hr, "CreateSurface(back) Windowed");

				// 3. Attach a Clipper so we don't draw over the Taskbar/Start Menu
				LPDIRECTDRAWCLIPPER clipper;
				hr = ddraw->lpVtbl->CreateClipper(ddraw, 0, &clipper, NULL);
				if (SUCCEEDED(hr)) {
						clipper->lpVtbl->SetHWnd(clipper, 0, hwnd);
						frontBuffer->lpVtbl->SetClipper(frontBuffer, clipper);
						clipper->lpVtbl->Release(clipper); // frontBuffer now owns the reference
				}
		}

		// --- Z-BUFFER: Works roughly the same for both now ---
		// Get the dimensions of the backBuffer to match the Z-Buffer size
		DDSURFACEDESC surfDesc = {0};
		surfDesc.dwSize = sizeof(DDSURFACEDESC);
		backBuffer->lpVtbl->GetSurfaceDesc(backBuffer, &surfDesc);

		int depths[] = { 32, 24, 16 };
		DWORD flags[] = { DDBD_32, DDBD_24, DDBD_16 };
		
		// 1. Try VRAM depths that the hardware actually claims to support
		for (int i = 0; i < 3; i++) {
				if (deviceZBitDepths && !(deviceZBitDepths & flags[i])) continue;

				DDSURFACEDESC zDesc = { 0 };
				zDesc.dwSize = sizeof(DDSURFACEDESC);
				zDesc.dwFlags = DDSD_CAPS | DDSD_WIDTH | DDSD_HEIGHT | DDSD_ZBUFFERBITDEPTH;
				zDesc.ddsCaps.dwCaps = DDSCAPS_ZBUFFER | DDSCAPS_VIDEOMEMORY;
				zDesc.dwWidth = surfDesc.dwWidth;
				zDesc.dwHeight = surfDesc.dwHeight;
				zDesc.dwZBufferBitDepth = depths[i];

				hr = ddraw->lpVtbl->CreateSurface(ddraw, &zDesc, &zBuffer, NULL);
				if (SUCCEEDED(hr)) {
						Platform_Log1("created VRAM z-buffer with %i bits", &depths[i]);
						hr = backBuffer->lpVtbl->AddAttachedSurface(backBuffer, zBuffer);
						if (SUCCEEDED(hr)) {
								depthBits = depths[i];
								return; // Success!
						} else {
								FatalError(hr, "AddAttachedSurface");
						}
						zBuffer->lpVtbl->Release(zBuffer);
						zBuffer = NULL;
				}
		}

		// 2. Fallback to SYSRAM if VRAM didn't work (this will likely trigger software rendering)
		for (int i = 0; i < 3; i++) {
				DDSURFACEDESC zDesc = { 0 };
				zDesc.dwSize = sizeof(DDSURFACEDESC);
				zDesc.dwFlags = DDSD_CAPS | DDSD_WIDTH | DDSD_HEIGHT | DDSD_ZBUFFERBITDEPTH;
				zDesc.ddsCaps.dwCaps = DDSCAPS_ZBUFFER | DDSCAPS_SYSTEMMEMORY;
				zDesc.dwWidth = surfDesc.dwWidth;
				zDesc.dwHeight = surfDesc.dwHeight;
				zDesc.dwZBufferBitDepth = depths[i];

				hr = ddraw->lpVtbl->CreateSurface(ddraw, &zDesc, &zBuffer, NULL);
				if (SUCCEEDED(hr)) {
						Platform_Log1("created SYSRAM z-buffer with %i bits", &depths[i]);
						hr = backBuffer->lpVtbl->AddAttachedSurface(backBuffer, zBuffer);
						if (SUCCEEDED(hr)) {
								depthBits = depths[i];
								return;
						} else {
								FatalError(hr, "AddAttachedSurface");
						}
						zBuffer->lpVtbl->Release(zBuffer);
						zBuffer = NULL;
				}
		}

		if (!zBuffer) FatalError(hr, "Create/Attach Z-Buffer");
}

void Gfx_Create(void) {
	HRESULT hr;
	IDirectDraw *pDD1 = NULL;
	Platform_LogConst("Creating D3D5 backend");

	Gfx.MaxTexWidth = 256;
	Gfx.MaxTexHeight = 256;
	Gfx.Created = true;
	Gfx.BackendType = CC_GFX_BACKEND_D3D5;
	//Gfx.Limitations = GFX_LIMIT_MAX_VERTEX_SIZE;
	Gfx.Limitations = 0;
	Gfx.Mipmaps = false;
	//Gfx.ManagedTextures = true;
	gfx_perspective = Options_GetBool("d3d5-perspective", true);
	gfx_textureson = Options_GetBool("d3d5-textureson", true);
	gfx_exclusive = Options_GetBool("d3d5-exclusive", false);
	gfx_forceload = Options_GetBool("d3d5-forceload", false);
	Gfx.NonPowTwoTexturesSupport = GFX_NONPOW2_NONE;

	DirectDrawEnumerate(DDEnumCallback, NULL);
	hr = DirectDrawCreate(g_FoundSecondary ? &g_DeviceGUID : NULL, &pDD1, NULL);
	if (FAILED(hr)) FatalError(hr, "DirectDrawCreate");

	hr = pDD1->lpVtbl->QueryInterface(pDD1, &IID_IDirectDraw2, (void **)&ddraw);
	pDD1->lpVtbl->Release(pDD1);
	if (FAILED(hr)) FatalError(hr, "QI IDirectDraw2");

	DDCAPS halCaps = { sizeof(DDCAPS) };
	ddraw->lpVtbl->GetCaps(ddraw, &halCaps, NULL);
	useLoadPattern = gfx_forceload || (halCaps.ddsCaps.dwCaps & DDSCAPS_ALLOCONLOAD) != 0;
	Platform_Log1("Load pattern active: %i", &useLoadPattern);


	hwnd = (HWND)Window_Main.Handle.ptr;
	WindowedMode = !gfx_exclusive || Window_GetWindowState() != WINDOW_STATE_FULLSCREEN;
	if (g_FoundSecondary && WindowedMode) WindowedMode = false;

	DWORD flags = WindowedMode ? DDSCL_NORMAL : (DDSCL_EXCLUSIVE | DDSCL_FULLSCREEN | DDSCL_ALLOWREBOOT);
	hr = ddraw->lpVtbl->SetCooperativeLevel(ddraw, hwnd, flags);
	if (FAILED(hr)) FatalError(hr, "SetCooperativeLevel");
	if (!WindowedMode) Gfx_SetDisplayMode();

	hr = ddraw->lpVtbl->QueryInterface(ddraw, &IID_IDirect3D2, (void **)&d3d);
	if (FAILED(hr)) FatalError(hr, "QI IDirect3D2");

	deviceZBitDepths = 0;
	d3d->lpVtbl->EnumDevices(d3d, EnumDeviceCallback, NULL);

	CreateSurfaces();
	cachedWidth  = Game.Width;
	cachedHeight = Game.Height;
	
	DDSURFACEDESC mode = { sizeof(DDSURFACEDESC) };
	if (SUCCEEDED(ddraw->lpVtbl->GetDisplayMode(ddraw, &mode))) {
			gfx_depth = mode.ddpfPixelFormat.dwRGBBitCount;
	}

	TryCreateDevice();

	/* Configure viewport */
	hr = d3d->lpVtbl->CreateViewport(d3d, &view, NULL);
	if (FAILED(hr)) FatalError(hr, "CreateViewport");
	device->lpVtbl->AddViewport(device, view);
	device->lpVtbl->SetCurrentViewport(device, view);
	Gfx_SetViewport(0, 0, Game.Width, Game.Height);

	Gfx_RestoreState();
}

void Gfx_Free(void) {
	Gfx_FreeState();

	if (device && view) device->lpVtbl->DeleteViewport(device, view);
	if (view) {
		view->lpVtbl->Release(view);
		view = NULL;
	}
	if (device) {
		device->lpVtbl->Release(device);
		device = NULL;
	}
	if (d3d) {
		d3d->lpVtbl->Release(d3d);
		d3d = NULL;
	}
	if (zBuffer) {
		zBuffer->lpVtbl->Release(zBuffer);
		zBuffer = NULL;
	}
	if (WindowedMode && backBuffer) {
		backBuffer->lpVtbl->Release(backBuffer);
	}
	backBuffer = NULL;
	if (frontBuffer) {
		frontBuffer->lpVtbl->Release(frontBuffer);
		frontBuffer = NULL;
	}
	if (ddraw) {
		ddraw->lpVtbl->Release(ddraw);
		ddraw = NULL;
	}
}

cc_bool Gfx_TryRestoreContext(void) {
	if (!ddraw) {
		Gfx_Create();
		return true;
	}
	
	cc_bool windowed = !gfx_exclusive || Window_GetWindowState() != WINDOW_STATE_FULLSCREEN;
	if (g_FoundSecondary) windowed = false;
	if (Game.Width != cachedWidth || Game.Height != cachedHeight || windowed != WindowedMode) {
			Gfx_FreeState();
			if (device && view) device->lpVtbl->DeleteViewport(device, view);
			if (device) { device->lpVtbl->Release(device); device = NULL; }
			if (zBuffer) { zBuffer->lpVtbl->Release(zBuffer); zBuffer = NULL; }
			if (WindowedMode && backBuffer) {
					backBuffer->lpVtbl->Release(backBuffer); 
			}
			backBuffer = NULL;
			if (frontBuffer) { 
					frontBuffer->lpVtbl->Release(frontBuffer); frontBuffer = NULL; 
			}
			
			if (windowed != WindowedMode) {
					if (!WindowedMode) ddraw->lpVtbl->RestoreDisplayMode(ddraw);
					WindowedMode = windowed;
					
					DWORD flags = WindowedMode ? DDSCL_NORMAL : (DDSCL_EXCLUSIVE | DDSCL_FULLSCREEN | DDSCL_ALLOWREBOOT);
					HRESULT hr = ddraw->lpVtbl->SetCooperativeLevel(ddraw, hwnd, flags);
					if (FAILED(hr)) FatalError(hr, "SetCooperativeLevel transition");
					
					if (!WindowedMode) {
							Gfx_SetDisplayMode();
					}
			} else if (!WindowedMode) {
					Gfx_SetDisplayMode();
			}

			cachedWidth = Game.Width;
			cachedHeight = Game.Height;
			
			CreateSurfaces();
			
			DDSURFACEDESC mode = { sizeof(DDSURFACEDESC) };
			if (SUCCEEDED(ddraw->lpVtbl->GetDisplayMode(ddraw, &mode))) {
					gfx_depth = mode.ddpfPixelFormat.dwRGBBitCount;
			}

			TryCreateDevice();
			
			if (view) {
					device->lpVtbl->AddViewport(device, view);
					device->lpVtbl->SetCurrentViewport(device, view);
			}
			
			Gfx_RecreateContext();
			Gfx_SetViewport(0, 0, Game.Width, Game.Height);
			return true;
	}

	if (frontBuffer && frontBuffer->lpVtbl->IsLost(frontBuffer) == DDERR_SURFACELOST) {
		frontBuffer->lpVtbl->Restore(frontBuffer);
		if (zBuffer) zBuffer->lpVtbl->Restore(zBuffer);
	}
	return true;
}

/*########################################################################################################################*
 *---------------------------------------------------------Textures--------------------------------------------------------*
 *#########################################################################################################################*/
typedef struct {
	IDirectDrawSurface *surface;    // VIDEOMEMORY
	IDirectDrawSurface *sysSurface; // SYSTEMMEMORY
	IDirect3DTexture2 *texture;     // VIDEOMEMORY texture
	IDirect3DTexture2 *sysTexture;  // SYSTEMMEMORY texture
	D3DTEXTUREHANDLE handle;
	IDirect3DDevice2 *lastDevice;
} D3D5Texture;

static HRESULT CALLBACK EnumTexFormatsCallback(LPDDSURFACEDESC pDDSD, LPVOID lpContext) {
		DDSURFACEDESC *bestFormat = (DDSURFACEDESC *)lpContext;
		LPDDPIXELFORMAT pfn = &pDDSD->ddpfPixelFormat;

		// --- Priority 1: ARGB 8888 (32-bit) ---
		// We check for 32-bit and ensure the Alpha mask is the top byte (0xFF000000)
		if (pfn->dwRGBBitCount == 32) {
				if ((pfn->dwFlags & DDPF_ALPHAPIXELS) && (pfn->dwRGBAlphaBitMask == 0xFF000000)) {
						*bestFormat = *pDDSD;
						return DDENUMRET_CANCEL; // Perfect match found, exit search
				}
		}

		// --- Priority 2: ARGB 1555 (16-bit) ---
		// If we haven't found a 32-bit format yet, this is our next best bet
		if (pfn->dwRGBBitCount == 16) {
				if ((pfn->dwFlags & DDPF_ALPHAPIXELS) && (pfn->dwRGBAlphaBitMask == 0x8000)) {
						// Only overwrite if the current bestFormat isn't already 32-bit
						if (bestFormat->ddpfPixelFormat.dwRGBBitCount != 32) {
								*bestFormat = *pDDSD;
						}
						// We don't CANCEL here because a 32-bit format might show up later in the enumeration
				}

				// --- Priority 3: RGB 565 (16-bit, no alpha) ---
				// Final fallback for compatibility
				if (!(pfn->dwFlags & DDPF_ALPHAPIXELS) && (pfn->dwRBitMask == 0xF800)) {
						if (bestFormat->ddpfPixelFormat.dwRGBBitCount == 0) { // Only set if empty
								*bestFormat = *pDDSD;
						}
				}
		}

		return DDENUMRET_OK;
}

static void CopyTextureData(DDSURFACEDESC* desc, DDSURFACEDESC* lockDesc, struct Bitmap* bmp, int rowWidth) {
	cc_uint8* dstRow = (cc_uint8*)lockDesc->lpSurface;
	BitmapCol* srcRow = bmp->scan0;
	int bpp = desc->ddpfPixelFormat.dwRGBBitCount;

	for (int y = 0; y < bmp->height; y++) {
		if (bpp == 32) {
			cc_uint32* dst = (cc_uint32*)dstRow;
			for (int x = 0; x < bmp->width; x++) dst[x] = srcRow[x];
		} else if (bpp == 16) {
			cc_uint16* dst = (cc_uint16*)dstRow;
			for (int x = 0; x < bmp->width; x++) {
				BitmapCol color = srcRow[x];
				int r = (PackedCol_R(color) * desc->ddpfPixelFormat.dwRBitMask) >> 8;
				int g = (PackedCol_G(color) * desc->ddpfPixelFormat.dwGBitMask) >> 8;
				int b = (PackedCol_B(color) * desc->ddpfPixelFormat.dwBBitMask) >> 8;
				int a = (PackedCol_A(color) > 128) ? desc->ddpfPixelFormat.dwRGBAlphaBitMask : 0;

				dst[x] = (cc_uint16)(a | (r & desc->ddpfPixelFormat.dwRBitMask) |
					(g & desc->ddpfPixelFormat.dwGBitMask) |
					(b & desc->ddpfPixelFormat.dwBBitMask));
			}
		}
		dstRow += lockDesc->lPitch;
		srcRow += rowWidth;
	}
}

GfxResourceID Gfx_AllocTexture(struct Bitmap *bmp, int rowWidth, cc_uint8 flags, cc_bool mipmaps) {
		DDSURFACEDESC format = {0};
		format.dwSize = sizeof(DDSURFACEDESC);
		device->lpVtbl->EnumTextureFormats(device, EnumTexFormatsCallback, &format);

		DDSURFACEDESC desc = {0};
		desc.dwSize = sizeof(DDSURFACEDESC);
		desc.dwFlags = DDSD_CAPS | DDSD_WIDTH | DDSD_HEIGHT | DDSD_PIXELFORMAT;
		desc.dwWidth  = bmp->width;
		desc.dwHeight = bmp->height;
		desc.ddpfPixelFormat = format.ddpfPixelFormat;

		if (useLoadPattern) {
				// 1. Create SYSTEM MEMORY surface
				desc.ddsCaps.dwCaps = DDSCAPS_TEXTURE | DDSCAPS_SYSTEMMEMORY;
				IDirectDrawSurface *sysSurface;
				HRESULT hr = ddraw->lpVtbl->CreateSurface(ddraw, &desc, &sysSurface, NULL);
				if (FAILED(hr)) return 0;

				// 2. Create VIDEO MEMORY surface
				desc.ddsCaps.dwCaps = DDSCAPS_TEXTURE | DDSCAPS_VIDEOMEMORY | DDSCAPS_ALLOCONLOAD;
				IDirectDrawSurface *vidSurface;
				hr = ddraw->lpVtbl->CreateSurface(ddraw, &desc, &vidSurface, NULL);
				if (FAILED(hr)) {
						sysSurface->lpVtbl->Release(sysSurface);
						return 0;
				}

				// 3. Fill SYSTEM MEMORY surface
				DDSURFACEDESC lockDesc = {0};
				lockDesc.dwSize = sizeof(DDSURFACEDESC);
				if (SUCCEEDED(sysSurface->lpVtbl->Lock(sysSurface, NULL, &lockDesc, DDLOCK_WAIT | DDLOCK_WRITEONLY, NULL))) {
						CopyTextureData(&desc, &lockDesc, bmp, rowWidth);
						sysSurface->lpVtbl->Unlock(sysSurface, NULL);
				}

				// 4. Wrap & Load
				IDirect3DTexture2 *sysTexture = NULL, *vidTexture = NULL;
				if (FAILED(sysSurface->lpVtbl->QueryInterface(sysSurface, &IID_IDirect3DTexture2, (void **)&sysTexture)) ||
						FAILED(vidSurface->lpVtbl->QueryInterface(vidSurface, &IID_IDirect3DTexture2, (void **)&vidTexture))) {
						if (vidTexture) vidTexture->lpVtbl->Release(vidTexture);
						if (sysTexture) sysTexture->lpVtbl->Release(sysTexture);
						vidSurface->lpVtbl->Release(vidSurface);
						sysSurface->lpVtbl->Release(sysSurface);
						return 0;
				}

				vidTexture->lpVtbl->Load(vidTexture, sysTexture);

				D3DTEXTUREHANDLE handle;
				if (FAILED(vidTexture->lpVtbl->GetHandle(vidTexture, device, &handle))) {
						vidTexture->lpVtbl->Release(vidTexture);
						sysTexture->lpVtbl->Release(sysTexture);
						vidSurface->lpVtbl->Release(vidSurface);
						sysSurface->lpVtbl->Release(sysSurface);
						return 0;
				}

				D3D5Texture *tex = Mem_TryAlloc(1, sizeof(D3D5Texture));
				if (!tex) {
						vidTexture->lpVtbl->Release(vidTexture);
						sysTexture->lpVtbl->Release(sysTexture);
						vidSurface->lpVtbl->Release(vidSurface);
						sysSurface->lpVtbl->Release(sysSurface);
						return 0;
				}
				tex->surface = vidSurface; tex->sysSurface = sysSurface;
				tex->texture = vidTexture; tex->sysTexture = sysTexture;
				tex->handle = handle; tex->lastDevice = device;

				if (!(flags & TEXTURE_FLAG_DYNAMIC)) {
						tex->sysTexture->lpVtbl->Release(tex->sysTexture);
						tex->sysTexture = NULL;
						tex->sysSurface->lpVtbl->Release(tex->sysSurface);
						tex->sysSurface = NULL;
				}
				return tex;
		} else {
				// Legacy linear copy path
				desc.ddsCaps.dwCaps = DDSCAPS_TEXTURE | DDSCAPS_VIDEOMEMORY;
				IDirectDrawSurface *vidSurface;
				HRESULT hr = ddraw->lpVtbl->CreateSurface(ddraw, &desc, &vidSurface, NULL);
				if (FAILED(hr)) return 0;

				DDSURFACEDESC lockDesc = {0};
				lockDesc.dwSize = sizeof(DDSURFACEDESC);
				if (SUCCEEDED(vidSurface->lpVtbl->Lock(vidSurface, NULL, &lockDesc, DDLOCK_WAIT | DDLOCK_WRITEONLY, NULL))) {
						CopyTextureData(&desc, &lockDesc, bmp, rowWidth);
						vidSurface->lpVtbl->Unlock(vidSurface, NULL);
				}

				IDirect3DTexture2 *vidTexture;
				if (FAILED(vidSurface->lpVtbl->QueryInterface(vidSurface, &IID_IDirect3DTexture2, (void **)&vidTexture))) {
						vidSurface->lpVtbl->Release(vidSurface);
						return 0;
				}

				D3DTEXTUREHANDLE handle;
				if (FAILED(vidTexture->lpVtbl->GetHandle(vidTexture, device, &handle))) {
						vidTexture->lpVtbl->Release(vidTexture);
						vidSurface->lpVtbl->Release(vidSurface);
						return 0;
				}

				D3D5Texture *tex = Mem_TryAlloc(1, sizeof(D3D5Texture));
				if (!tex) {
						vidTexture->lpVtbl->Release(vidTexture);
						vidSurface->lpVtbl->Release(vidSurface);
						return 0;
				}
				tex->surface = vidSurface; tex->sysSurface = NULL;
				tex->texture = vidTexture; tex->sysTexture = NULL;
				tex->handle = handle; tex->lastDevice = device;
				return tex;
		}
}

void Gfx_UpdateTexture(GfxResourceID texId, int x, int y, struct Bitmap *part,
											 int rowWidth, cc_bool mipmaps) {
		if (Gfx.LostContext) return;
		D3D5Texture *tex = (D3D5Texture *)texId;
		DDSURFACEDESC lockDesc = { 0 };
		lockDesc.dwSize = sizeof(DDSURFACEDESC);
		
		IDirectDrawSurface* target = useLoadPattern ? tex->sysSurface : tex->surface;
		if (!target) return;

		RECT rect = { x, y, x + part->width, y + part->height };
		HRESULT hr = target->lpVtbl->Lock(target, &rect, &lockDesc, DDLOCK_WAIT, NULL);
		if (FAILED(hr)) return;

		DDSURFACEDESC surfDesc = { 0 };
		surfDesc.dwSize = sizeof(DDSURFACEDESC);
		target->lpVtbl->GetSurfaceDesc(target, &surfDesc);

		CopyTextureData(&surfDesc, &lockDesc, part, rowWidth);
		target->lpVtbl->Unlock(target, NULL);

		if (useLoadPattern) {
				tex->texture->lpVtbl->Load(tex->texture, tex->sysTexture);
		}
}

#define MAX_PENDING_TEXTURES 256
static D3D5Texture* pendingDeletions[MAX_PENDING_TEXTURES];
static int numPendingDeletions = 0;

static void FreePendingTextures(void) {
		if (numPendingDeletions == 0) return;
		//Platform_Log1("Freeing %i pending textures", &numPendingDeletions);
		if (!Gfx.LostContext && device)
				device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_TEXTUREHANDLE, 0);
		for (int i = 0; i < numPendingDeletions; i++) {
				D3D5Texture *tex = pendingDeletions[i];
				if (tex->texture)    tex->texture->lpVtbl->Release(tex->texture);
				if (tex->sysTexture) tex->sysTexture->lpVtbl->Release(tex->sysTexture);
				if (tex->surface)    tex->surface->lpVtbl->Release(tex->surface);
				if (tex->sysSurface) tex->sysSurface->lpVtbl->Release(tex->sysSurface);
				Mem_Free(tex);
		}
		numPendingDeletions = 0;
}

void Gfx_DeleteTexture(GfxResourceID *texId) {
		if (!texId || !(*texId)) return;
		D3D5Texture *tex = (D3D5Texture *)(*texId);

		if (numPendingDeletions >= MAX_PENDING_TEXTURES) {
				Platform_LogConst("Pending textures filled");
				FreePendingTextures();
		}

		pendingDeletions[numPendingDeletions++] = tex;
		*texId = NULL;
}

void Gfx_EnableMipmaps(void) {}
void Gfx_DisableMipmaps(void) {}

void Gfx_BindTexture(GfxResourceID texId) {
	if (Gfx.LostContext || !gfx_textureson) return;
	D3D5Texture *tex = (D3D5Texture *)texId;
	if (tex && tex->lastDevice != device) {
			tex->texture->lpVtbl->GetHandle(tex->texture, device, &tex->handle);
			tex->lastDevice = device;
	}
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_TEXTUREHANDLE, tex ? tex->handle : 0);
}

/*########################################################################################################################*
*-----------------------------------------------------State management----------------------------------------------------*
*#########################################################################################################################*/
static D3DFOGMODE gfx_fogMode = D3DFOG_NONE;
static cc_bool gfx_depthTesting, gfx_depthWriting;
static PackedCol gfx_clearColor, gfx_fogColor;
static float gfx_fogEnd = -1.0f, gfx_fogDensity = -1.0f;

void Gfx_SetFaceCulling(cc_bool enabled) {
	if (Gfx.LostContext) return;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_CULLMODE, enabled ? D3DCULL_CW : D3DCULL_NONE);
}

void Gfx_SetFog(cc_bool enabled) {
	if (gfx_fogEnabled == enabled) return;
	gfx_fogEnabled = enabled;

	if (Gfx.LostContext) return;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_FOGENABLE, enabled);
}

void Gfx_SetFogCol(PackedCol color) {
	if (color == gfx_fogColor) return;
	gfx_fogColor = color;

	if (Gfx.LostContext) return;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_FOGCOLOR, PACKED_TO_D3DCOLOR(color));
}

void Gfx_SetFogDensity(float value) {
	if (value == gfx_fogDensity) return;
	gfx_fogDensity = value;

	if (Gfx.LostContext) return;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_FOGTABLEDENSITY, *(DWORD *)&value);
}

void Gfx_SetFogEnd(float value) {
	if (value == gfx_fogEnd) return;
	gfx_fogEnd = value;

	if (Gfx.LostContext) return;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_FOGTABLEEND, *(DWORD *)&value);
}

void Gfx_SetFogMode(FogFunc func) {
	D3DFOGMODE mode = func == FOG_LINEAR
												? D3DFOG_LINEAR
												: (func == FOG_EXP ? D3DFOG_EXP : D3DFOG_EXP2);
	if (mode == gfx_fogMode) return;

	gfx_fogMode = mode;
	if (Gfx.LostContext) return;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_FOGTABLEMODE, mode);
}

void SetAlphaTest(cc_bool enabled) {
	if (Gfx.LostContext) return;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ALPHATESTENABLE, enabled);
}

void SetAlphaBlend(cc_bool enabled) {
	if (Gfx.LostContext) return;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ALPHABLENDENABLE, enabled);
}

void Gfx_SetAlphaArgBlend(cc_bool enabled) {}

void Gfx_ClearColor(PackedCol color) {
		gfx_clearColor = color;
}

static DWORD GetFillColor(PackedCol color, DDPIXELFORMAT* pf) {
	cc_uint8 r = PackedCol_R(color);
	cc_uint8 g = PackedCol_G(color);
	cc_uint8 b = PackedCol_B(color);
	cc_uint8 a = PackedCol_A(color);

	if (pf->dwFlags & DDPF_PALETTEINDEXED8) return 0;

	// For 24-bit and 32-bit, we usually assume the standard layout,
	// but 16-bit (565/555) absolutely needs manual bit manipulation.
	if (pf->dwRGBBitCount == 32 && pf->dwRBitMask == 0xFF0000 && pf->dwGBitMask == 0xFF00 && pf->dwBBitMask == 0xFF) {
		return color;
	}

	DWORD res = 0;
	static const int components[] = { 0, 8, 16, 24 }; // B, G, R, A positions in PackedCol
	DWORD masks[] = { pf->dwBBitMask, pf->dwGBitMask, pf->dwRBitMask, pf->dwRGBAlphaBitMask };
	cc_uint8 vals[] = { b, g, r, a };

	for (int i = 0; i < 4; i++) {
		DWORD mask = masks[i];
		if (!mask) continue;

		DWORD tempMask = mask;
		int shift = 0;
		while (!(tempMask & 1)) { tempMask >>= 1; shift++; }
		res |= (((DWORD)vals[i] * tempMask) / 255) << shift;
	}
	return res;
}

void Gfx_ClearBuffers(GfxBuffers buffers) {
		HRESULT hr;
		if (Gfx.LostContext) return;
		
		// 1. Clear the Color Buffer using a ColorFill Blt
		if (buffers & GFX_BUFFER_COLOR) {
				DDBLTFX ddbltfx = { 0 };
				ddbltfx.dwSize = sizeof(DDBLTFX);
				
				DDSURFACEDESC desc = { sizeof(DDSURFACEDESC) };
				backBuffer->lpVtbl->GetSurfaceDesc(backBuffer, &desc);
				ddbltfx.dwFillColor = GetFillColor(gfx_clearColor, &desc.ddpfPixelFormat);

				// Blit to the backBuffer (not the front!)
				// Passing NULL for the destination RECT clears the entire surface
				hr = backBuffer->lpVtbl->Blt(backBuffer, NULL, NULL, NULL, 
																		 DDBLT_COLORFILL | DDBLT_WAIT, &ddbltfx);
				if (FAILED(hr)) FatalError(hr, "Blt ColorFill Failed");
		}

		// 2. Clear the Z-Buffer
		// Most D3D5 hardware prefers the viewport clear for Z-buffers 
		// because it handles 16-bit/24-bit conversion internally.
		if (buffers & GFX_BUFFER_DEPTH) {
				D3DRECT rect = { 0, 0, Game.Width, Game.Height };
				
				// We only pass D3DCLEAR_ZBUFFER here
				hr = view->lpVtbl->Clear(view, 1, &rect, D3DCLEAR_ZBUFFER);
				if (FAILED(hr)) FatalError(hr, "Z-Buffer Clear Failed");
		}
}

void Gfx_SetDepthTest(cc_bool enabled) {
	gfx_depthTesting = enabled;
	if (Gfx.LostContext) return;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ZENABLE, enabled);
}

void Gfx_SetDepthWrite (cc_bool enabled) {
	gfx_depthWriting = enabled;
	if (Gfx.LostContext) return;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ZWRITEENABLE, enabled);
}

static void SetColorWrite(cc_bool r, cc_bool g, cc_bool b, cc_bool a) {}

void Gfx_DepthOnlyRendering(cc_bool depthOnly) {
	if (Gfx.LostContext) return;
	if (depthOnly) {
		device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_TEXTUREHANDLE, 0);
		device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_SRCBLEND,  D3DBLEND_ZERO);
		device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_DESTBLEND, D3DBLEND_ONE);
		Gfx_SetAlphaBlending(true);
		device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ALPHATESTENABLE, FALSE);
	} else {
		device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_SRCBLEND,  D3DBLEND_SRCALPHA);
		device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_DESTBLEND, D3DBLEND_INVSRCALPHA);
	}
}

/*########################################################################################################################*
*-------------------------------------------------------Index buffers-----------------------------------------------------*
*#########################################################################################################################*/
static void *gfx_indexBuffer;

 GfxResourceID Gfx_CreateIb2(int count, Gfx_FillIBFunc fillFunc, void *obj) {
	cc_uint16 *indices = Mem_TryAlloc(count, sizeof(cc_uint16));
	if (indices)
		fillFunc(indices, count, obj);
	return indices;
}

void Gfx_BindIb(GfxResourceID ib) { gfx_indexBuffer = ib; }

void Gfx_DeleteIb(GfxResourceID *ib) {
	Mem_Free(*ib);
	*ib = NULL;
}

/*########################################################################################################################*
*------------------------------------------------------Vertex buffers-----------------------------------------------------*
*#########################################################################################################################*/
static D3DVERTEXTYPE d3d5_vertexType;
static void *gfx_vertices;
static int buf_count;
static VertexFormat buf_fmt;

static GfxResourceID Gfx_AllocStaticVb(VertexFormat fmt, int count) {
	return Mem_TryAlloc(count, sizeof(D3DLVERTEX));
}

void Gfx_BindVb(GfxResourceID vb) { gfx_vertices = vb; }

void Gfx_DeleteVb(GfxResourceID *vb) {
	GfxResourceID data = *vb;
	if (data)
		Mem_Free(data);
	*vb = 0;
}

void *Gfx_LockVb(GfxResourceID vb, VertexFormat fmt, int count) {
	buf_fmt = fmt;
	buf_count = count;
	return vb;
}

void Gfx_UnlockVb(GfxResourceID vb) {
	D3DLVERTEX *dst = (D3DLVERTEX *)vb;
	
	if (buf_fmt == VERTEX_FORMAT_TEXTURED) {
		struct VertexTextured *src = (struct VertexTextured *)vb;

		for (int i = buf_count - 1; i >= 0; i--) {
			float x = src[i].x, y = src[i].y, z = src[i].z;
			cc_uint32 col = src[i].Col;
			float u = src[i].U, v = src[i].V;

			dst[i].x = x;
			dst[i].y = y;
			dst[i].z = z;
			dst[i].dwReserved = 0;
			dst[i].color = col;
			dst[i].specular = 0;
			dst[i].tu = u;
			dst[i].tv = v;
		}
	} else {
		struct VertexColoured *src = (struct VertexColoured *)vb;
		for (int i = buf_count - 1; i >= 0; i--) {
			float x = src[i].x, y = src[i].y, z = src[i].z;
			cc_uint32 col = src[i].Col;

			dst[i].x = x;
			dst[i].y = y;
			dst[i].z = z;
			dst[i].dwReserved = 0;
			dst[i].color = col;
			dst[i].specular = 0;
			dst[i].tu = 0.0f;
			dst[i].tv = 0.0f;
		}
	}
}

void Gfx_SetVertexFormat(VertexFormat fmt) { 
	if (fmt == gfx_format) return;
	gfx_format = fmt;
	if (fmt == VERTEX_FORMAT_COLOURED) {
		device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_TEXTUREHANDLE, 0);
	}
	gfx_stride = strideSizes[fmt];

	d3d5_vertexType = D3DVT_LVERTEX;
}

void Gfx_DrawVb_Lines(int verticesCount) {
	if (Gfx.LostContext) return;
	if (!gfx_vertices)
		return;
	device->lpVtbl->DrawPrimitive(device, D3DPT_LINELIST, d3d5_vertexType,
																gfx_vertices, verticesCount, 0);
}

void Gfx_DrawVb_IndexedTris(int verticesCount) {  
	if (Gfx.LostContext) return;
	if (!gfx_vertices || !gfx_indexBuffer) return;
	if (verticesCount > 65535) Process_Abort("Too many vertices");
	int indicesCount = (verticesCount >> 1) * 3;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_TEXTUREPERSPECTIVE, gfx_perspective);
	device->lpVtbl->DrawIndexedPrimitive(device, D3DPT_TRIANGLELIST, 
																			 d3d5_vertexType, gfx_vertices, verticesCount,
																			 gfx_indexBuffer, indicesCount, 0);
}

void Gfx_DrawVb_IndexedTris_Range(int verticesCount, int startVertex, DrawHints hints) {
	if (Gfx.LostContext) return;
	if (!gfx_vertices || !gfx_indexBuffer) return;
	if (verticesCount > 65535) Process_Abort("Too many vertices");
	int indicesCount = (verticesCount >> 1) * 3;
	D3DLVERTEX *ptr = (D3DLVERTEX *)gfx_vertices + startVertex;
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_TEXTUREPERSPECTIVE, gfx_perspective && !(hints & (DRAW_HINT_SPRITE | DRAW_HINT_RECT)));
	device->lpVtbl->DrawIndexedPrimitive(device, D3DPT_TRIANGLELIST,
																			 d3d5_vertexType, ptr, verticesCount,
																			 gfx_indexBuffer, indicesCount, 0);
}

void Gfx_DrawIndexedTris_T2fC4b(int verticesCount, int startVertex) {
	if (!gfx_vertices || !gfx_indexBuffer)
		return;
	Gfx_DrawVb_IndexedTris_Range(verticesCount, startVertex, 0);
}

/*########################################################################################################################*
 *---------------------------------------------------------Matrices--------------------------------------------------------*
 *#########################################################################################################################*/
void Gfx_LoadMatrix(MatrixType type, const struct Matrix *matrix) {
	if (Gfx.LostContext) return;
	D3DMATRIX d3dMat;
	MatrixToD3D(&d3dMat, matrix);

	D3DTRANSFORMSTATETYPE state = type == MATRIX_PROJ
																		? D3DTRANSFORMSTATE_PROJECTION
																		: D3DTRANSFORMSTATE_VIEW;
	device->lpVtbl->SetTransform(device, state, &d3dMat);
	if (type == MATRIX_PROJ)
		_proj = d3dMat;
	if (type == MATRIX_VIEW)
		_view = d3dMat;
}

void Gfx_LoadMVP(const struct Matrix *view, const struct Matrix *proj,
								 struct Matrix *mvp) {
	Gfx_LoadMatrix(MATRIX_VIEW, view);
	Gfx_LoadMatrix(MATRIX_PROJ, proj);
	Matrix_Mul(mvp, view, proj);
}

void Gfx_EnableTextureOffset(float x, float y) { /* No-op */ }

void Gfx_DisableTextureOffset(void) { /* No-op */ }

void Gfx_CalcOrthoMatrix(struct Matrix *matrix, float width, float height,
												 float zNear, float zFar) {
	float adjustX, adjustY;
	*matrix = Matrix_Identity;

	adjustX = 0.5 * ( 2.0f / width);
	adjustY = 0.5 * (-2.0f / height);

	matrix->row1.x = 2.0f / width;
	matrix->row2.y = -2.0f / height;
	matrix->row3.z = 1.0f / (zNear - zFar);

	matrix->row4.x = -1.0f - adjustX;
	matrix->row4.y =  1.0f - adjustY;
	matrix->row4.z = zNear / (zNear - zFar);
}

static float Cotangent(float x) { return Math_CosF(x) / Math_SinF(x); }
void Gfx_CalcPerspectiveMatrix(struct Matrix* matrix, float fov, float aspect, float zFar) {
	float zNear = 0.1f;

	/* Source https://learn.microsoft.com/en-us/windows/win32/direct3d9/d3dxmatrixperspectivefovrh */
	/* NOTE: This calculation is shared with Direct3D 11 backend */
	float c = Cotangent(0.5f * fov);
	*matrix = Matrix_Identity;

	matrix->row1.x =  c / aspect;
	matrix->row2.y =  c;
	matrix->row3.z = zFar / (zNear - zFar);
	matrix->row3.w = -1.0f;
	matrix->row4.z = (zNear * zFar) / (zNear - zFar);
	matrix->row4.w =  0.0f;
}

void Gfx_BeginFrame(void) { 
		if (Gfx.LostContext) return;
		device->lpVtbl->BeginScene(device); 
}

void Gfx_EndFrame(void) {
		if (Gfx.LostContext) return;
		device->lpVtbl->EndScene(device);

		if (WindowedMode) {
				RECT rect;
				POINT pt = { 0, 0 };

				// 1. Get the size of just the game canvas (e.g., 800x600)
				GetClientRect(hwnd, &rect);

				// 2. Convert (0,0) from window-space to screen-space
				ClientToScreen(hwnd, &pt);

				// 3. Offset the rectangle so it points to the right spot on the monitor
				OffsetRect(&rect, pt.x, pt.y);

				// 4. Blit only to that specific interior area
				frontBuffer->lpVtbl->Blt(frontBuffer, &rect, backBuffer, NULL, DDBLT_WAIT, NULL);
		} else {
				frontBuffer->lpVtbl->Flip(frontBuffer, NULL, DDFLIP_WAIT);
		}
		FreePendingTextures();
}

void Gfx_OnWindowResize(void) {
	if (Game.Width == cachedWidth && Game.Height == cachedHeight) return;
	Gfx_LoseContext(" (resizing window)");
}

void Gfx_SetViewport(int x, int y, int w, int h) {
	D3DVIEWPORT2 vpDesc = {0};
	vpDesc.dwSize = sizeof(D3DVIEWPORT2);
	vpDesc.dwX = x;
	vpDesc.dwY = y;
	vpDesc.dwWidth = w;
	vpDesc.dwHeight = h;
	vpDesc.dvClipX = -1.0f;
	vpDesc.dvClipY = 1.0f;
	vpDesc.dvClipWidth = 2.0f;
	vpDesc.dvClipHeight = 2.0f;
	vpDesc.dvMinZ = 0.0f;
	vpDesc.dvMaxZ = 1.0f;
	
	view->lpVtbl->SetViewport2(view, &vpDesc);
}

void Gfx_GetApiInfo(cc_string *info) {
	int pointerSize = sizeof(void*) * 8;
	String_Format1(info, "-- Direct3D 5.0 (%i bit) --\n", &pointerSize);
	String_Format1(info, "Device type: %c\n", deviceIsSoftware ? "Software (RGB)" : "Hardware (HAL)");
	
	DDSURFACEDESC mode = { 0 };
	mode.dwSize = sizeof(DDSURFACEDESC);
	if (SUCCEEDED(ddraw->lpVtbl->GetDisplayMode(ddraw, &mode))) {
			String_Format3(info, "Display mode: %i x %i (%i bpp)\n", &mode.dwWidth, &mode.dwHeight, &mode.ddpfPixelFormat.dwRGBBitCount);
	}
	
	String_Format1(info, "Window status: %c\n", WindowedMode ? "Windowed" : "Exclusive Fullscreen");

	DWORD total, free;
	DDSCAPS caps = { DDSCAPS_VIDEOMEMORY };
	if (SUCCEEDED(ddraw->lpVtbl->GetAvailableVidMem(ddraw, &caps, &total, &free))) {
			float fTotal = total / (1024.0f * 1024.0f);
			float fFree  = free  / (1024.0f * 1024.0f);
			String_Format2(info, "Video memory: %f2 MB total, %f2 free\n", &fTotal, &fFree);
	}

	PrintMaxTextureInfo(info);
	String_Format4(info, "NP2 support: %b, Perspective: %b, Textures: %b, Load: %b\n", &Gfx.NonPowTwoTexturesSupport, &gfx_perspective, &gfx_textureson, &useLoadPattern);
	String_Format1(info, "Depth buffer bits: %i", &depthBits);
}

cc_bool Gfx_WarnIfNecessary(void) { 
		if (deviceIsSoftware) {
				Chat_AddRaw("&cSoftware rendering is being used, performance will greatly suffer.");
				return true;
		}
		return false; 
}

static cc_bool GetPerspective(void) { return gfx_perspective; }
static void SetPerspective(cc_bool v) { 
		gfx_perspective = v; 
		Options_SetBool("d3d5-perspective", v);
}

static cc_bool GetTexturesOn(void) { return gfx_textureson; }
static void SetTexturesOn(cc_bool v) { 
		gfx_textureson = v; 
		Options_SetBool("d3d5-textureson", v);
}

static cc_bool GetExclusive(void) { return gfx_exclusive; }
static void SetExclusive(cc_bool v) { 
		gfx_exclusive = v; 
		Options_SetBool("d3d5-exclusive", v);
		if (device) Gfx_LoseContext(" (toggling exclusive fullscreen)");
}

static cc_bool GetForceLoad(void) { return gfx_forceload; }
static void SetForceLoad(cc_bool v) { 
		gfx_forceload = v; 
		Options_SetBool("d3d5-forceload", v);
		if (device) Gfx_LoseContext(" (toggling forced load)");
}

cc_bool Gfx_GetUIOptions(struct MenuOptionsScreen* s) { 
		MenuOptionsScreen_AddBool(s, "Perspective correct", GetPerspective, SetPerspective, 
		"Prefer perspective correct texturing to be on or off.\n" \
		"Most graphics cards will override this option.");
		/*
		MenuOptionsScreen_AddBool(s, "Enable textures", GetTexturesOn, SetTexturesOn, 
		"Disable when the clown vomit gets to ya");
		*/
		MenuOptionsScreen_AddBool(s, "Exclusive fullscreen", GetExclusive, SetExclusive, 
		"Whether to use exclusive fullscreen mode when in fullscreen mode,\n" \
		"rather than borderless window mode.");
		MenuOptionsScreen_AddBool(s, "Force Load pattern", GetForceLoad, SetForceLoad, 
		"Use an alternate method to load textures.\n" \
		"If you get scrambled textures try this");
		return true; // hide mipmap option
}

cc_result Gfx_TakeScreenshot(struct Stream* output) { return 0; }
void Gfx_SetFpsLimit(cc_bool vsync, float minFrameMs) {}

void Gfx_SetVSync(cc_bool vsync) {
	if (gfx_vsync == vsync) return;
	gfx_vsync = vsync;
	if (device) Gfx_LoseContext(" (toggling VSync)");
}

void Gfx_SetScissor(int x, int y, int width, int height) {}

static void Gfx_FreeState(void) { 
	FreePendingTextures();
	FreeDefaultResources();
	cachedWidth  = 0;
	cachedHeight = 0;
}

static void Gfx_RestoreState(void) { 
	InitDefaultResources();
	gfx_format = -1;

	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ZFUNC, D3DCMP_LESSEQUAL);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ALPHAREF,  127);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ALPHAFUNC, D3DCMP_GREATEREQUAL);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_SRCBLEND,  D3DBLEND_SRCALPHA);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_DESTBLEND, D3DBLEND_INVSRCALPHA);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_TEXTUREMAPBLEND, D3DTBLEND_MODULATEALPHA);
	
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ALPHATESTENABLE,   gfx_alphaTest);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ALPHABLENDENABLE, gfx_alphaBlend);

	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_FOGENABLE, gfx_fogEnabled);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_FOGCOLOR,  PACKED_TO_D3DCOLOR(gfx_fogColor));
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_FOGTABLEDENSITY, *(DWORD *)&gfx_fogDensity);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_FOGTABLEEND, *(DWORD *)&gfx_fogEnd);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_FOGTABLEMODE, gfx_fogMode);

	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ZENABLE,      gfx_depthTesting);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_ZWRITEENABLE, gfx_depthWriting);
	device->lpVtbl->SetRenderState(device, D3DRENDERSTATE_DITHERENABLE, gfx_depth < 32);
}


#endif
