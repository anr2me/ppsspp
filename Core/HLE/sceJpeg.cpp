// Copyright (c) 2012- PPSSPP Project.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, version 2.0 or later versions.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License 2.0 for more details.

// A copy of the GPL 2.0 should have been included with the program.
// If not, see http://www.gnu.org/licenses/

// Official git repository and contact information can be found at
// https://github.com/hrydgard/ppsspp and http://www.ppsspp.org/.

#include <algorithm>
#include "ext/jpge/jpgd.h"

#include "Common/CommonTypes.h"
#include "Common/Serialize/Serializer.h"
#include "Common/Serialize/SerializeFuncs.h"
#include "Core/Debugger/MemBlockInfo.h"
#include "Core/HLE/HLE.h"
#include "Core/HLE/FunctionWrappers.h"
#include "Core/HLE/sceJpeg.h"
#include "Core/HLE/sceKernel.h"
#include "GPU/GPUCommon.h"
#include "Core/MemMap.h"
#include "Core/Reporting.h"

// Uncomment if you want to dump JPEGs loaded through sceJpeg to a file
// #define JPEG_DEBUG
#ifdef JPEG_DEBUG
#include "ext/xxhash.h"
#endif

struct u24_be {
	unsigned char value[3];

	operator unsigned int() {
		return 0x00000000 | (value[0] << 16) | (value[1] << 8) | (value[2] << 0);
	}
};

static int mjpegInited = 0;
static int mjpegWidth = 0;
static int mjpegHeight = 0;

void __JpegInit() {
	mjpegInited = 0;
	mjpegWidth = 0;
	mjpegHeight = 0;
}

enum : uint32_t {
	ERROR_JPEG_INVALID_DATA = 0x80650004,
	ERROR_JPEG_INVALID_COLORSPACE = 0x80650013,
	ERROR_JPEG_INVALID_SIZE = 0x80650020,
	ERROR_JPEG_NO_SOI = 0x80650023,
	ERROR_JPEG_INVALID_STATE = 0x80650039,
	ERROR_JPEG_OUT_OF_MEMORY = 0x80650041,
	ERROR_JPEG_ALREADY_INIT = 0x80650042,
	ERROR_JPEG_INVALID_VALUE = 0x80650051,
};

void __JpegDoState(PointerWrap &p) {
	auto s = p.Section("sceJpeg", 1, 2);
	if (!s)
		return;

	Do(p, mjpegWidth);
	Do(p, mjpegHeight);
	if (s >= 2) {
		Do(p, mjpegInited);
	} else {
		mjpegInited = -1;
	}
}

static int getWidthHeight(int width, int height) {
	return (width << 16) | height;
}

// TODO: sceJpegCsc and sceJpegMJpegCsc use different factors.
static u32 convertYCbCrToABGR(int y, int cb, int cr) {
	//see http://en.wikipedia.org/wiki/Yuv#Y.27UV444_to_RGB888_conversion for more information.
	cb = cb - 128;
	cr = cr - 128;
	int r = y + cr + (cr >> 2) + (cr >> 3) + (cr >> 5);
	int g = y - ((cb >> 2) + (cb >> 4) + (cb >> 5)) - ((cr >> 1) + (cr >> 3) + (cr >> 4) + (cr >> 5));
	int b = y + cb + (cb >> 1) + (cb >> 2) + (cb >> 6);

	// check rgb value.
	if (r > 0xFF) r = 0xFF; if(r < 0) r = 0;
	if (g > 0xFF) g = 0xFF; if(g < 0) g = 0;
	if (b > 0xFF) b = 0xFF; if(b < 0) b = 0;

	return (b << 16) | (g << 8) | (r << 0);
}

static int JpegCsc(u32 imageAddr, u32 yCbCrAddr, int widthHeight, int bufferWidth, uint32_t chroma, int &usec) {
	if ((chroma & 0x000FFFFF) != 0x00020202 && (chroma & 0x000FFFFF) != 0x00020201 && (chroma & 0x000FFFFF) != 0x00020101)
		return hleLogError(ME, ERROR_JPEG_INVALID_COLORSPACE, "invalid colorspace");
	if (bufferWidth < 0)
		bufferWidth = 0;

	int height = widthHeight & 0xFFFF;
	int width = (widthHeight >> 16) & 0xFFFF;
	if (height == 0)
		height = 1;

	uint8_t widthShift = ((chroma >> 8) & 0x03) - 1;
	uint8_t heightShift = (chroma & 0x03) - 1;
	int sizeY = width * height;
	int sizeCb = sizeY >> (widthShift + heightShift);

	uint64_t destSize = ((uint64_t)bufferWidth * (height - 1) + width) * 4;
	if (destSize > 0x3FFFFFFF || !Memory::IsValidRange(imageAddr, (uint32_t)destSize))
		return hleLogError(ME, ERROR_JPEG_INVALID_VALUE, "invalid dest address or size");
	if (sizeY > 0x3FFFFFFF || !Memory::IsValidRange(yCbCrAddr, sizeY + sizeCb + sizeCb))
		return hleLogError(ME, ERROR_JPEG_INVALID_VALUE, "invalid src address or size");

	u32_le *imageBuffer = (u32_le *)Memory::GetPointerWriteUnchecked(imageAddr);
	const u8 *Y = (const u8 *)Memory::GetPointerUnchecked(yCbCrAddr);
	const u8 *Cb = Y + sizeY;
	const u8 *Cr = Cb + sizeCb;

	// Very approximate estimate based on tests on a PSP.  Usually under.
	usec += 60 + 6 * height + width / 2 + width / 4;

	if ((widthHeight & 0x00010001) == 0 && height > 1) {
		for (int y = 0; y < height; y += 2) {
			for (int x = 0; x < width; x += 2) {
				u8 y0 = Y[width * y + x];
				u8 y1 = Y[width * y + x + 1];
				u8 y2 = Y[width * (y + 1) + x];
				u8 y3 = Y[width * (y + 1) + x + 1];
				u8 cb = Cb[(width >> widthShift) * (y >> heightShift) + (x >> widthShift)];
				u8 cr = Cr[(width >> widthShift) * (y >> heightShift) + (x >> widthShift)];

				imageBuffer[bufferWidth * y + x + 0] = convertYCbCrToABGR(y0, cb, cr);
				imageBuffer[bufferWidth * y + x + 1] = convertYCbCrToABGR(y1, cb, cr);
				imageBuffer[bufferWidth * (y + 1) + x] = convertYCbCrToABGR(y2, cb, cr);
				imageBuffer[bufferWidth * (y + 1) + x + 1] = convertYCbCrToABGR(y3, cb, cr);
			}
		}
	} else {
		for (int y = 0; y < height; ++y) {
			for (int x = 0; x < width; ++x) {
				u8 yy = Y[width * y + x];
				u8 cb = Cb[(width >> widthShift) * (y >> heightShift) + (x >> widthShift)];
				u8 cr = Cr[(width >> widthShift) * (y >> heightShift) + (x >> widthShift)];

				imageBuffer[bufferWidth * y + x] = convertYCbCrToABGR(yy, cb, cr);
			}
		}
	}

	NotifyMemInfo(MemBlockFlags::READ, yCbCrAddr, sizeY + sizeCb + sizeCb, "JpegCsc");
	NotifyMemInfo(MemBlockFlags::WRITE, imageAddr, (uint32_t)destSize, "JpegCsc");

	if ((widthHeight & 0xFFFF) == 0)
		return hleLogSuccessI(ME, -1);
	return hleLogSuccessI(ME, 0);
}

static int JpegMJpegCsc(u32 imageAddr, u32 yCbCrAddr, int widthHeight, int bufferWidth, int &usec) {
	int height = widthHeight & 0xFFFF;
	int width = (widthHeight >> 16) & 0xFFFF;
	if (bufferWidth < 0)
		bufferWidth = bufferWidth > -901 ? 901 + bufferWidth : 0;
	if (height == 0)
		height = 1;

	uint8_t widthShift = 1;
	uint8_t heightShift = 1;
	int sizeY = width * height;
	int sizeCb = sizeY >> 2;

	if (width > 720 || height > 480)
		return hleLogError(ME, ERROR_JPEG_INVALID_SIZE, "invalid size, max 720x480");
	if (bufferWidth > 1024)
		return hleLogError(ME, ERROR_JPEG_INVALID_SIZE, "invalid stride, max 1024");
	uint32_t destSize = (bufferWidth * (height - 1) + width) * 4;
	if (!Memory::IsValidRange(imageAddr, destSize))
		return hleLogError(ME, SCE_KERNEL_ERROR_INVALID_POINTER, "invalid dest address or size");

	u32_le *imageBuffer = (u32_le *)Memory::GetPointerWriteUnchecked(imageAddr);
	const u8 *Y = (const u8 *)Memory::GetPointerUnchecked(yCbCrAddr);
	const u8 *Cb = Y + sizeY;
	const u8 *Cr = Cb + sizeCb;

	// Very approximate estimate based on tests on a PSP.  Usually under.
	// The PSP behaves strangely for heights below 16, not rescheduling and writing fewer bytes.
	if (height >= 16) {
		usec += 9 * height;
	}

	if (!Memory::IsValidRange(yCbCrAddr, sizeY + sizeCb + sizeCb)) {
		// Seems to write based on zeros?  Maybe reuses some other value?
		for (int y = 0; y < height; ++y) {
			for (int x = 0; x < width; ++x) {
				imageBuffer[bufferWidth * y + x] = convertYCbCrToABGR(0, 0, 0);
			}
		}
	} else if ((widthHeight & 0x00030000) == 0) {
		for (int y = 0; y < height; ++y) {
			for (int x = 0; x < width; x += 4) {
				int offset = width * y + x;
				u8 y0 = Y[offset + 0];
				u8 y1 = Y[offset + 1];
				u8 y2 = Y[offset + 2];
				u8 y3 = Y[offset + 3];
				u8 cb = Cb[offset >> 2];
				u8 cr = Cr[offset >> 2];

				imageBuffer[bufferWidth * y + x + 0] = convertYCbCrToABGR(y0, cb, cr);
				imageBuffer[bufferWidth * y + x + 1] = convertYCbCrToABGR(y1, cb, cr);
				imageBuffer[bufferWidth * y + x + 2] = convertYCbCrToABGR(y2, cb, cr);
				imageBuffer[bufferWidth * y + x + 3] = convertYCbCrToABGR(y3, cb, cr);
			}
		}
		NotifyMemInfo(MemBlockFlags::READ, yCbCrAddr, sizeY + sizeCb + sizeCb, "JpegMJpegCsc");
	} else {
		for (int y = 0; y < height; ++y) {
			for (int x = 0; x < width; ++x) {
				int offset = width * y + x;
				u8 yy = Y[offset];
				u8 cb = Cb[offset >> 2];
				u8 cr = Cr[offset >> 2];

				imageBuffer[bufferWidth * y + x] = convertYCbCrToABGR(yy, cb, cr);
			}
		}
		NotifyMemInfo(MemBlockFlags::READ, yCbCrAddr, sizeY + sizeCb + sizeCb, "JpegMJpegCsc");
	}

	NotifyMemInfo(MemBlockFlags::WRITE, imageAddr, destSize, "JpegMJpegCsc");

	return hleLogSuccessI(ME, 0);
}

static int sceJpegMJpegCsc(u32 imageAddr, u32 yCbCrAddr, int widthHeight, int bufferWidth) {
	if (mjpegInited == 0)
		return hleLogError(ME, 0x80000001, "not yet inited");

	int usec = 0;
	int result = JpegMJpegCsc(imageAddr, yCbCrAddr, widthHeight, bufferWidth, usec);
	
	int width = (widthHeight >> 16) & 0xFFF;
	int height = widthHeight & 0xFFF;
	if (result >= 0)
		gpu->NotifyVideoUpload(imageAddr, width * height * 4, width, GE_FORMAT_8888);

	if (usec != 0)
		return hleDelayResult(result, "jpeg csc", usec);
	return result;
}

static u32 convertARGBtoABGR(u32 argb) {
	return ((argb & 0xFF00FF00)) | ((argb & 0x000000FF) << 16) | ((argb & 0x00FF0000) >> 16);
}

static int DecodeJpeg(u32 jpegAddr, int jpegSize, u32 imageAddr, int &usec) {
	if (!Memory::IsValidRange(jpegAddr, jpegSize))
		return hleLogError(ME, ERROR_JPEG_NO_SOI, "invalid jpeg address");
	if (jpegSize == 0)
		return hleLogError(ME, ERROR_JPEG_INVALID_DATA, "invalid jpeg data");

	NotifyMemInfo(MemBlockFlags::READ, jpegAddr, jpegSize, "JpegDecodeMJpeg");

	const u8 *buf = Memory::GetPointerUnchecked(jpegAddr);
	if (jpegSize < 2 || buf[0] != 0xFF || buf[1] != 0xD8)
		return hleLogError(ME, ERROR_JPEG_NO_SOI, "no SOI found, invalid data");

	int width, height, actual_components;
	unsigned char *jpegBuf = jpgd::decompress_jpeg_image_from_memory(buf, jpegSize, &width, &height, &actual_components, 3);

	if (actual_components != 3 && actual_components != 1) {
		// The assumption that the image was RGB was wrong...
		// Try again.
		int components = actual_components;
		jpegBuf = jpgd::decompress_jpeg_image_from_memory(buf, jpegSize, &width, &height, &actual_components, components);
	}

	if (jpegBuf == nullptr) {
		return hleLogError(ME, ERROR_JPEG_INVALID_DATA, "unable to decompress jpeg");
	}

	usec += (width * height) / 14;

	if (!Memory::IsValidRange(imageAddr, mjpegWidth * mjpegHeight * 4)) {
		free(jpegBuf);
		return hleLogError(ME, SCE_KERNEL_ERROR_INVALID_POINTER, "invalid output address");
	}
	// Note: even if you Delete, the size is still allowed.
	if (width > mjpegWidth || height > mjpegHeight) {
		free(jpegBuf);
		return hleLogError(ME, ERROR_JPEG_INVALID_SIZE, "invalid output address");
	}
	if (mjpegInited == 0) {
		// If you finish after setting the size, then call this - you get an interesting error.
		free(jpegBuf);
		return hleLogError(ME, 0x80000001, "mjpeg not inited");
	}

	usec += (width * height) / 110;

	if (actual_components == 3 || actual_components == 1) {
		u24_be *imageBuffer = (u24_be*)jpegBuf;
		u32_le *abgr = (u32_le *)Memory::GetPointerUnchecked(imageAddr);
		for (int y = 0; y < height; ++y) {
			for (int x = 0; x < width; x++)	{
				abgr[x] = convertARGBtoABGR(imageBuffer[x]);
			}
			imageBuffer += width;
			abgr += mjpegWidth;
		}
		NotifyMemInfo(MemBlockFlags::WRITE, imageAddr, mjpegWidth * height, "JpegDecodeMJpeg");
	}

	free(jpegBuf);
	return hleLogSuccessI(ME, getWidthHeight(width, height));
}

static int sceJpegDecodeMJpeg(u32 jpegAddr, int jpegSize, u32 imageAddr, int dhtMode) {
	if ((jpegAddr | jpegSize | (jpegAddr + jpegSize)) & 0x80000000)
		return hleLogError(ME, SCE_KERNEL_ERROR_PRIV_REQUIRED, "invalid jpeg address");
	if (imageAddr & 0x80000000)
		return hleLogError(ME, SCE_KERNEL_ERROR_PRIV_REQUIRED, "invalid output address");

	int usec = 300;
	int result = DecodeJpeg(jpegAddr, jpegSize, imageAddr, usec);
	return hleDelayResult(result, "jpeg decode", usec);
}

static int sceJpegDecodeMJpegSuccessively(u32 jpegAddr, int jpegSize, u32 imageAddr, int dhtMode) {
	if ((jpegAddr | jpegSize | (jpegAddr + jpegSize)) & 0x80000000)
		return hleLogError(ME, SCE_KERNEL_ERROR_PRIV_REQUIRED, "invalid jpeg address");
	if (imageAddr & 0x80000000)
		return hleLogError(ME, SCE_KERNEL_ERROR_PRIV_REQUIRED, "invalid output address");

	int usec = 300;
	int result = DecodeJpeg(jpegAddr, jpegSize, imageAddr, usec);
	return hleDelayResult(result, "jpeg decode", usec);
}

static int sceJpegCsc(u32 imageAddr, u32 yCbCrAddr, int widthHeight, int bufferWidth, int colourInfo) {
	int usec = 0;
	int result = JpegCsc(imageAddr, yCbCrAddr, widthHeight, bufferWidth, colourInfo, usec);
	if (usec != 0)
		return hleDelayResult(result, "jpeg csc", usec);
	return result;
}

static int getYCbCrBufferSize(int w, int h) {
	// Return necessary buffer size for conversion: 12 bits per pixel
	return ((w * h) >> 1) * 3;
}

static int JpegGetOutputInfo(u32 jpegAddr, int jpegSize, u32 colourInfoAddr) {
	if (!Memory::IsValidRange(jpegAddr, jpegSize))
		return hleLogError(ME, ERROR_JPEG_NO_SOI, "invalid jpeg address");
	if (jpegSize == 0)
		return hleLogError(ME, ERROR_JPEG_INVALID_DATA, "invalid jpeg data");

	NotifyMemInfo(MemBlockFlags::READ, jpegAddr, jpegSize, "JpegGetOutputInfo");

	const u8 *buf = Memory::GetPointerUnchecked(jpegAddr);
	if (jpegSize < 2 || buf[0] != 0xFF || buf[1] != 0xD8)
		return hleLogError(ME, ERROR_JPEG_NO_SOI, "no SOI found, invalid data");

	int width, height, actual_components;
	unsigned char *jpegBuf = jpgd::decompress_jpeg_image_from_memory(buf, jpegSize, &width, &height, &actual_components, 3);

	if (actual_components != 3 && actual_components != 1) {
		// The assumption that the image was RGB was wrong...
		// Try again.
		int components = actual_components;
		jpegBuf = jpgd::decompress_jpeg_image_from_memory(buf, jpegSize, &width, &height, &actual_components, components);
	}

	if (jpegBuf == nullptr) {
		return hleLogError(ME, ERROR_JPEG_INVALID_DATA, "unable to decompress jpeg");
	}

	free(jpegBuf);
	
	// Buffer to store info about the color space in use.
	// - Bits 24 to 32 (Always empty): 0x00
	// - Bits 16 to 24 (Color mode): 0x00 (Unknown), 0x01 (Greyscale) or 0x02 (YCbCr) 
	// - Bits 8 to 16 (Vertical chroma subsampling value): 0x00, 0x01 or 0x02
	// - Bits 0 to 8 (Horizontal chroma subsampling value): 0x00, 0x01 or 0x02
	if (Memory::IsValidAddress(colourInfoAddr)) {
		// Note: can't actually seem to get any other subsampling values or color modes to work on a PSP.
		Memory::Write_U32(0x00020202, colourInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, colourInfoAddr, 4, "JpegGetOutputInfo");
	}

#ifdef JPEG_DEBUG
		char jpeg_fname[256];
		const u8 *jpegDumpBuf = Memory::GetPointer(jpegAddr);
		u32 jpeg_xxhash = XXH32((const char *)jpegDumpBuf, jpegSize, 0xC0108888);
		sprintf(jpeg_fname, "Jpeg\\%X.jpg", jpeg_xxhash);
		FILE *wfp = fopen(jpeg_fname, "wb");
		if (!wfp) {
			_wmkdir(L"Jpeg\\");
			wfp = fopen(jpeg_fname, "wb");
		}
		fwrite(jpegDumpBuf, 1, jpegSize, wfp);
		fclose(wfp);
#endif //JPEG_DEBUG

	return hleLogSuccessI(ME, getYCbCrBufferSize(width, height));
}

static int sceJpegGetOutputInfo(u32 jpegAddr, int jpegSize, u32 colourInfoAddr, int dhtMode) {
	if ((jpegAddr | jpegSize | (jpegAddr + jpegSize)) & 0x80000000)
		return hleLogError(ME, SCE_KERNEL_ERROR_PRIV_REQUIRED, "invalid jpeg address");

	int result = JpegGetOutputInfo(jpegAddr, jpegSize, colourInfoAddr);
	// Time taken varies a bit, this is the low end.  Depends on data.
	// Note that errors delay as well.
	return hleDelayResult(result, "jpeg get output info", 250);
}

static u32 convertRGBToYCbCr(u32 rgb) {
	//see http://en.wikipedia.org/wiki/Yuv#Y.27UV444_to_RGB888_conversion for more information.
	u8  r = (rgb >> 16) & 0xFF;
	u8  g = (rgb >>  8) & 0xFF;
	u8  b = (rgb >>  0) & 0xFF;
	int  y = 0.299f * r + 0.587f * g + 0.114f * b + 0;
	int cb = -0.169f * r - 0.331f * g + 0.499f * b + 128.0f;
	int cr = 0.499f * r - 0.418f * g - 0.0813f * b + 128.0f;

	// check yCbCr value
	if ( y > 0xFF)  y = 0xFF; if ( y < 0)  y = 0;
	if (cb > 0xFF) cb = 0xFF; if (cb < 0) cb = 0;
	if (cr > 0xFF) cr = 0xFF; if (cr < 0) cr = 0;

	return (y << 16) | (cb << 8) | cr;
}

static int JpegConvertRGBToYCbCr(const void *data, u8 *output, int width, int height) {
	u24_be *imageBuffer = (u24_be *)data;
	int sizeY = width * height;
	int sizeCb = sizeY >> 2;
	u8 *Y = output;
	u8 *Cb = Y + sizeY;
	u8 *Cr = Cb + sizeCb;

	for (int y = 0; y < height; ++y) {
		for (int x = 0; x < width; x += 4) {
			u32 abgr0 = imageBuffer[x + 0];
			u32 abgr1 = imageBuffer[x + 1];
			u32 abgr2 = imageBuffer[x + 2];
			u32 abgr3 = imageBuffer[x + 3];

			u32 yCbCr0 = convertRGBToYCbCr(abgr0);
			u32 yCbCr1 = convertRGBToYCbCr(abgr1);
			u32 yCbCr2 = convertRGBToYCbCr(abgr2);
			u32 yCbCr3 = convertRGBToYCbCr(abgr3);
			
			Y[x + 0] = (yCbCr0 >> 16) & 0xFF;
			Y[x + 1] = (yCbCr1 >> 16) & 0xFF;
			Y[x + 2] = (yCbCr2 >> 16) & 0xFF;
			Y[x + 3] = (yCbCr3 >> 16) & 0xFF;

			*Cb++ = (yCbCr0 >> 8) & 0xFF;
			*Cr++ = yCbCr0 & 0xFF;
		}
		imageBuffer += width;
		Y += width;
	}
	return getWidthHeight(width, height);
}

static int JpegDecodeMJpegYCbCr(u32 jpegAddr, int jpegSize, u32 yCbCrAddr, int yCbCrSize, int &usec) {
	if (!Memory::IsValidRange(jpegAddr, jpegSize))
		return hleLogError(ME, ERROR_JPEG_NO_SOI, "invalid jpeg address");
	if (jpegSize == 0)
		return hleLogError(ME, ERROR_JPEG_INVALID_DATA, "invalid jpeg data");

	NotifyMemInfo(MemBlockFlags::READ, jpegAddr, jpegSize, "JpegDecodeMJpegYCbCr");

	const u8 *buf = Memory::GetPointerUnchecked(jpegAddr);
	if (jpegSize < 2 || buf[0] != 0xFF || buf[1] != 0xD8)
		return hleLogError(ME, ERROR_JPEG_NO_SOI, "no SOI found, invalid data");

	int width, height, actual_components;
	unsigned char *jpegBuf = jpgd::decompress_jpeg_image_from_memory(buf, jpegSize, &width, &height, &actual_components, 3);

	if (actual_components != 3 && actual_components != 1) {
		// The assumption that the image was RGB was wrong...
		// Try again.
		int components = actual_components;
		jpegBuf = jpgd::decompress_jpeg_image_from_memory(buf, jpegSize, &width, &height, &actual_components, components);
	}

	if (jpegBuf == nullptr) {
		return hleLogError(ME, ERROR_JPEG_INVALID_DATA, "unable to decompress jpeg");
	}

	if (yCbCrSize < getYCbCrBufferSize(width, height)) {
		free(jpegBuf);
		return hleLogError(ME, ERROR_JPEG_OUT_OF_MEMORY, "buffer not large enough");
	}

	// Technically, it seems like the PSP doesn't support grayscale, but we might as well.
	if (actual_components == 3 || actual_components == 1) {
		if (Memory::IsValidRange(yCbCrAddr, getYCbCrBufferSize(width, height))) {
			JpegConvertRGBToYCbCr(jpegBuf, Memory::GetPointerWriteUnchecked(yCbCrAddr), width, height);
			NotifyMemInfo(MemBlockFlags::WRITE, yCbCrAddr, getYCbCrBufferSize(width, height), "JpegDecodeMJpegYCbCr");
		} else {
			// There's some weird behavior on the PSP where it writes data around the last passed address.
			WARN_LOG_REPORT(ME, "JpegDecodeMJpegYCbCr: Invalid output address (%08x / %08x) for %dx%d", yCbCrAddr, yCbCrSize, width, height);
		}
	}

	free(jpegBuf);

	// Rough estimate based on observed timing.
	usec += (width * height) / 14;
	return hleLogSuccessI(ME, getWidthHeight(width, height));
}

static int sceJpegDecodeMJpegYCbCr(u32 jpegAddr, int jpegSize, u32 yCbCrAddr, int yCbCrSize, int dhtMode) {
	if ((jpegAddr | jpegSize | (jpegAddr + jpegSize)) & 0x80000000)
		return hleLogError(ME, SCE_KERNEL_ERROR_PRIV_REQUIRED, "invalid jpeg address");
	if ((yCbCrAddr | yCbCrSize | (yCbCrAddr + yCbCrSize)) & 0x80000000)
		return hleLogError(ME, SCE_KERNEL_ERROR_PRIV_REQUIRED, "invalid output address");
	if (!Memory::IsValidRange(jpegAddr, jpegSize))
		return hleLogError(ME, ERROR_JPEG_INVALID_VALUE, "invalid jpeg address");
	
	int usec = 300;
	int result = JpegDecodeMJpegYCbCr(jpegAddr, jpegSize, yCbCrAddr, yCbCrSize, usec);
	return hleDelayResult(result, "jpeg decode", usec);
}

static int sceJpegDecodeMJpegYCbCrSuccessively(u32 jpegAddr, int jpegSize, u32 yCbCrAddr, int yCbCrSize, int dhtMode) {
	if ((jpegAddr | jpegSize | (jpegAddr + jpegSize)) & 0x80000000)
		return hleLogError(ME, SCE_KERNEL_ERROR_PRIV_REQUIRED, "invalid jpeg address");
	if ((yCbCrAddr | yCbCrSize | (yCbCrAddr + yCbCrSize)) & 0x80000000)
		return hleLogError(ME, SCE_KERNEL_ERROR_PRIV_REQUIRED, "invalid output address");
	
	// Do as same way as sceJpegDecodeMJpegYCbCr() but with smaller block size
	int usec = 300;
	int result = JpegDecodeMJpegYCbCr(jpegAddr, jpegSize, yCbCrAddr, yCbCrSize, usec);
	return hleDelayResult(result, "jpeg decode", usec);
}

static int sceJpeg_9B36444C() {
	ERROR_LOG_REPORT(ME, "UNIMPL sceJpeg_9B36444C()");
	return 0;
}

static int sceJpegCreateMJpeg(int width, int height) {
	if (mjpegInited == 0)
		return hleLogError(ME, ERROR_JPEG_INVALID_STATE, "not yet inited");
	if (mjpegInited == 2)
		return hleLogError(ME, ERROR_JPEG_INVALID_STATE, "already created");
	if (width > 1024)
		return hleLogError(ME, ERROR_JPEG_INVALID_SIZE, "width outside bounds");

	mjpegInited = 2;
	mjpegWidth = width;
	mjpegHeight = height;

	return hleLogSuccessInfoI(ME, 0);
}

static int sceJpegDeleteMJpeg() {
	if (mjpegInited == 0)
		return hleLogError(ME, ERROR_JPEG_INVALID_STATE, "not yet inited");
	if (mjpegInited == 1)
		return hleLogError(ME, ERROR_JPEG_INVALID_STATE, "not yet created");

	mjpegInited = 1;
	return hleLogSuccessInfoI(ME, 0);
}

static int sceJpegInitMJpeg() {
	if (mjpegInited == 1 || mjpegInited == 2)
		return hleLogError(ME, ERROR_JPEG_ALREADY_INIT, "already inited");

	// If it was -1, it's from an old save state, avoid double init error but assume inited.
	if (mjpegInited == 0)
		mjpegInited = 1;
	return hleLogSuccessI(ME, hleDelayResult(0, "mjpeg init", 130));
}

static int sceJpegFinishMJpeg() {
	if (mjpegInited == 0)
		return hleLogError(ME, ERROR_JPEG_INVALID_STATE, "already inited");
	if (mjpegInited == 2)
		return hleLogError(ME, ERROR_JPEG_INVALID_STATE, "mjpeg not deleted");

	// Even from an old save state, if we see this we leave compat mode.
	mjpegInited = 0;
	return hleLogSuccessI(ME, hleDelayResult(0, "mjpeg finish", 120));
}

static int sceJpegMJpegCscWithColorOption() {
	ERROR_LOG_REPORT(ME, "UNIMPL sceJpegMJpegCscWithColorOption()");
	return 0;
}

static int sceJpegDecompressAllImage() {
	ERROR_LOG_REPORT(ME, "UNIMPL sceJpegDecompressAllImage()");
	return 0;
}

void JpegNotifyLoadStatus(int state) {
	if (state == -1) {
		// Reset our state on unload.
		__JpegInit();
	}
}

const HLEFunction sceJpeg[] =
{
	{0X0425B986, &WrapI_V<sceJpegDecompressAllImage>,               "sceJpegDecompressAllImage",           'i', ""     },
	{0X04B5AE02, &WrapI_UUII<sceJpegMJpegCsc>,                      "sceJpegMJpegCsc",                     'i', "xxxi" },
	{0X04B93CEF, &WrapI_UIUI<sceJpegDecodeMJpeg>,                   "sceJpegDecodeMJpeg",                  'i', "xixi" },
	{0X227662D7, &WrapI_UIUII<sceJpegDecodeMJpegYCbCrSuccessively>, "sceJpegDecodeMJpegYCbCrSuccessively", 'i', "xixii"},
	{0X48B602B7, &WrapI_V<sceJpegDeleteMJpeg>,                      "sceJpegDeleteMJpeg",                  'i', ""     },
	{0X64B6F978, &WrapI_UIUI<sceJpegDecodeMJpegSuccessively>,       "sceJpegDecodeMJpegSuccessively",      'i', "xixi" },
	{0X67F0ED84, &WrapI_UUIII<sceJpegCsc>,                          "sceJpegCsc",                          'i', "xxxix"},
	{0X7D2F3D7F, &WrapI_V<sceJpegFinishMJpeg>,                      "sceJpegFinishMJpeg",                  'i', ""     },
	{0X8F2BB012, &WrapI_UIUI<sceJpegGetOutputInfo>,                 "sceJpegGetOutputInfo",                'x', "xipi" },
	{0X91EED83C, &WrapI_UIUII<sceJpegDecodeMJpegYCbCr>,             "sceJpegDecodeMJpegYCbCr",             'i', "xixii"},
	{0X9B36444C, &WrapI_V<sceJpeg_9B36444C>,                        "sceJpeg_9B36444C",                    'i', ""     },
	{0X9D47469C, &WrapI_II<sceJpegCreateMJpeg>,                     "sceJpegCreateMJpeg",                  'i', "ii"   },
	{0XAC9E70E6, &WrapI_V<sceJpegInitMJpeg>,                        "sceJpegInitMJpeg",                    'i', ""     },
	{0XA06A75C4, &WrapI_V<sceJpegMJpegCscWithColorOption>,          "sceJpegMJpegCscWithColorOption",      'i', ""     },
};

void Register_sceJpeg() {
	RegisterModule("sceJpeg", ARRAY_SIZE(sceJpeg), sceJpeg);
}
