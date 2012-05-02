/*
 * Asterisk -- An open source telephony toolkit.
 *
 * Copyright (C) 2012, Luka Perkov
 * Copyright (C) 2012, John Crispin
 *
 * Luka Perkov <openwrt@lukaperkov.net>
 * John Crispin <blogic@openwrt.org>
 *
 * See http://www.asterisk.org for more information about
 * the Asterisk project. Please do not directly contact
 * any of the maintainers of this project for assistance;
 * the project provides a web site, mailing lists and IRC
 * channels for your use.
 *
 * This program is free software, distributed under the terms of
 * the GNU General Public License Version 2. See the LICENSE file
 * at the top of the source tree.
 *
 */

/* asterisk includes */
#include "asterisk.h"

#include "asterisk/channel.h"
#include "asterisk/config.h"
#include "asterisk/logger.h"
#include "asterisk/module.h"

/* linux includes */
#include <fcntl.h>
#include <sys/stat.h>

/* tapi includes */
#include <drv_tapi/drv_tapi_io.h>
#include <drv_vmmc/vmmc_io.h>

/* tapi defines */
#define TAPI_AUDIO_PORT_NUM             2
#define TAPI_LL_DEV_BASE_PATH		"/dev/vmmc"
#define TAPI_LL_DEV_FIRMWARE_NAME	"/lib/firmware/danube_firmware.bin"
#define TAPI_LL_BBD_NAME		"/lib/firmware/danube_bbd_fxs.bin"
#define TAPI_ERROR			-1
#define TAPI_OK				0

/* tapi tones */
#define TAPI_TONE_LOCALE_NONE                   32
#define TAPI_TONE_LOCALE_BUSY_CODE              33
#define TAPI_TONE_LOCALE_CONGESTION_CODE        34
#define TAPI_TONE_LOCALE_DIAL_CODE              35
#define TAPI_TONE_LOCALE_RING_CODE              36
#define TAPI_TONE_LOCALE_WAITING_CODE           37

typedef struct
{ 
	int32_t dev_fd; 
	int32_t ch_fd[TAPI_AUDIO_PORT_NUM]; 
} tapi_ctx; 

tapi_ctx dev_ctx;

ASTERISK_FILE_VERSION(__FILE__, "$Revision: xxx_dev $")

static const char desc[] = "Lantiq TAPI FXS Channel";
static const char type[] = "TAPI";
static const char tdesc[] = "Lantiq TAPI FXS Channel Driver";

static const struct ast_channel_tech tapi_tech = {
	.type		= type,
	.description	= tdesc,
};

AST_MUTEX_DEFINE_STATIC(interface_lock);
AST_MUTEX_DEFINE_STATIC(ioctl_lock);

static int32_t
tapi_dev_open(const char *dev_path, const int32_t ch_num)
{
        char devname[FILENAME_MAX];
        memset(devname, 0, sizeof(devname));
        sprintf(devname,"%s%u%u\0", dev_path, 1, ch_num);
ast_log(LOG_ERROR, "tapi_dev_open : %s\n", devname);
        return open((const char*)devname, O_RDWR, 0644);
}

static int32_t
tapi_dev_binary_buffer_create(const char *path, uint8_t **ppBuf, uint32_t *pBufSz)
{
        FILE *fd;
        struct stat file_stat;
        int32_t status = TAPI_OK;

        fd = fopen(path, "rb");
        if (fd == NULL) {
                ast_log(LOG_ERROR, "binary file %s open failed\n", path);
                return TAPI_ERROR;
        }

        if (stat(path, &file_stat) != 0) {
                ast_log(LOG_ERROR, "file %s statistics get failed\n", path);
                return TAPI_ERROR;
        }

        *ppBuf = malloc(file_stat.st_size);
        if (*ppBuf == NULL) {
                ast_log(LOG_ERROR, "binary file %s memory allocation failed\n", path);
                status = TAPI_ERROR;
                goto on_exit;
        }

        if (fread (*ppBuf, sizeof(uint8_t), file_stat.st_size, fd) <= 0) {
                ast_log(LOG_ERROR, "file %s read failed\n", path);
                status = TAPI_ERROR;
                goto on_exit;
        }

        *pBufSz = file_stat.st_size;

on_exit:
        if (fd != NULL)
                fclose(fd);

        if (*ppBuf != NULL && status != TAPI_OK)
                free(*ppBuf);

        return status;
}

static void
tapi_dev_binary_buffer_delete(uint8_t *pBuf)
{
        if (pBuf != NULL)
                free(pBuf);
}

static int32_t
tapi_dev_firmware_download(int32_t fd, const char *path)
{
        int32_t status;
        uint8_t *pFirmware = NULL;
        uint32_t binSz = 0;
        VMMC_IO_INIT vmmc_io_init;

        status = tapi_dev_binary_buffer_create(path, &pFirmware, &binSz);
        if (status != TAPI_OK) {
                ast_log(LOG_ERROR, "binary buffer create failed!\n");
                return TAPI_ERROR;
        }

        memset(&vmmc_io_init, 0, sizeof(VMMC_IO_INIT));
        vmmc_io_init.pPRAMfw = pFirmware;
        vmmc_io_init.pram_size = binSz;

        status = ioctl(fd, FIO_FW_DOWNLOAD, &vmmc_io_init);
        if (status != TAPI_OK) {
                ast_log(LOG_ERROR, "FIO_FW_DOWNLOAD ioctl failed!\n");
                return TAPI_ERROR;
        }

        tapi_dev_binary_buffer_delete(pFirmware);

        return status;
}


static int
load_module(void)
{
	/* TODO: make this debug error */
	ast_log(LOG_ERROR, "entered load_module\n");

	IFX_TAPI_TONE_t tone;
	IFX_TAPI_DEV_START_CFG_t dev_start;
	IFX_TAPI_MAP_DATA_t map_data;
	IFX_TAPI_ENC_CFG_t enc_cfg;
	IFX_TAPI_LINE_VOLUME_t line_vol;
	IFX_TAPI_WLEC_CFG_t lec_cfg;
	IFX_TAPI_JB_CFG_t jb_cfg;
	IFX_TAPI_CID_CFG_t cid_cfg;
	int32_t status;
	uint8_t c, hook_status;

	if (ast_mutex_lock(&interface_lock)) {
		ast_log(LOG_ERROR, "unable to lock interface list\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	/* open device */
	dev_ctx.dev_fd = tapi_dev_open(TAPI_LL_DEV_BASE_PATH, 0);

	if (dev_ctx.dev_fd < 0) {
		ast_log(LOG_ERROR, "tapi device open function failed\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	for (c = 0; c < TAPI_AUDIO_PORT_NUM; c++) {
		dev_ctx.ch_fd[c] = tapi_dev_open(TAPI_LL_DEV_BASE_PATH, TAPI_AUDIO_PORT_NUM - c);

		if (dev_ctx.ch_fd[c] < 0) {
			ast_log(LOG_ERROR, "tapi channel %d open function failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}
	}

	status = ioctl(dev_ctx.dev_fd, IFX_TAPI_DEV_STOP, 0);
	if (status != TAPI_OK) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEV_STOP ioctl failed\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	status = tapi_dev_firmware_download(dev_ctx.dev_fd, TAPI_LL_DEV_FIRMWARE_NAME);
	if (status != TAPI_OK) {
		ast_log(LOG_ERROR, "voice firmware download failed\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	memset(&dev_start, 0x0, sizeof(IFX_TAPI_DEV_START_CFG_t));
	dev_start.nMode = IFX_TAPI_INIT_MODE_VOICE_CODER;

	/* Start TAPI */
	status = ioctl(dev_ctx.dev_fd, IFX_TAPI_DEV_START, &dev_start);
	if (status != TAPI_OK) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEV_START ioctl failed\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	/* tones */
	memset(&tone, 0, sizeof(IFX_TAPI_TONE_t));
	for (c = 0; c < TAPI_AUDIO_PORT_NUM; c++) {
//		status = ioctl(dev_ctx.ch_fd[c], IFX_TAPI_TONE_TABLE_CFG_SET, &tone);
//		if (status != TAPI_OK) {
//			ast_log(LOG_ERROR, "IFX_TAPI_TONE_TABLE_CFG_SET %d failed\n", c);
//			return AST_MODULE_LOAD_FAILURE;
//		}

		/* perform mapping */
		memset(&map_data, 0x0, sizeof(IFX_TAPI_MAP_DATA_t));
		map_data.nDstCh = c & 0x1 ? 0 : 1;
		map_data.nChType = IFX_TAPI_MAP_TYPE_PHONE;

		status = ioctl(dev_ctx.ch_fd[c], IFX_TAPI_MAP_DATA_ADD, &map_data);
		if (status != TAPI_OK) {
			ast_log(LOG_ERROR, "IFX_TAPI_MAP_DATA_ADD %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}

		/* Set Line feed */
		status = ioctl(dev_ctx.ch_fd[c], IFX_TAPI_LINE_FEED_SET, IFX_TAPI_LINE_FEED_STANDBY);
		if (status != TAPI_OK) {
			ast_log(LOG_ERROR, "IFX_TAPI_LINE_FEED_SET %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}


		/* ring demo */
		status = ioctl(dev_ctx.ch_fd[c], IFX_TAPI_RING_STOP, 0);
		if (status != TAPI_OK) {
			ast_log(LOG_ERROR, "IFX_TAPI_RING_STOP %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}
		status = ioctl(dev_ctx.ch_fd[c], IFX_TAPI_RING_START, 0);
		if (status != TAPI_OK) {
			ast_log(LOG_ERROR, "IFX_TAPI_RING_START %d failed!\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}
	}

	ast_mutex_unlock(&interface_lock);

	return AST_MODULE_LOAD_SUCCESS;
}

static int
unload_module(void)
{
	/* TODO: make this debug error */
	ast_log(LOG_ERROR, "entered unload_module\n");
	return 0;
}

AST_MODULE_INFO_STANDARD(ASTERISK_GPL_KEY, "Lantiq TAPI Channel");
