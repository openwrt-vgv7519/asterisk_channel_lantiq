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

int32_t ch_fd[TAPI_AUDIO_PORT_NUM];

typedef struct
{ 
	int32_t dev_fd; 
	int32_t ch_fd[TAPI_AUDIO_PORT_NUM]; 
	int8_t data2phone_map[TAPI_AUDIO_PORT_NUM]; 
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

/* TODO: make this also int8_t */
static int32_t
tapi_dev_open(char* dev_path, const int32_t ch_num)
{
        char devname[128] = { 0 };
        sprintf(devname,"%s%u%u", dev_path, 1, ch_num);
        return open((const char*)devname, 0x1103, 0644);
}

static int8_t
tapi_dev_binary_buffer_create(const char *path, uint8_t **ppBuf, uint32_t *pBufSz)
{
        int8_t status = TAPI_OK;
        FILE *fd;
        struct stat file_stat;

        fd = fopen(path, "rb");
        if (fd == NULL) {
                ast_log(LOG_ERROR, "binary file %s open failed!\n", path);
                return TAPI_ERROR;
        }

        if (stat(path, &file_stat) != 0) {
                ast_log(LOG_ERROR, "file %s statistics get failed!\n", path);
                return TAPI_ERROR;
        }

        *ppBuf = malloc(file_stat.st_size);
        if (*ppBuf == NULL) {
                ast_log(LOG_ERROR, "binary file %s memory allocation failed!\n", path);
                status = TAPI_ERROR;
                goto on_exit;
        }

        if (fread (*ppBuf, sizeof(uint8_t), file_stat.st_size, fd) <= 0) {
                ast_log(LOG_ERROR, "file %s read failed!\n", path);
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

static int8_t
tapi_dev_firmware_download(int32_t fd, const char *path)
{
        int32_t status = TAPI_OK;
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
        if (status != TAPI_OK)
                ast_log(LOG_ERROR, "FIO_FW_DOWNLOAD ioctl failed!\n");

        tapi_dev_binary_buffer_delete(pFirmware);

        return status;
}


static int load_module(void)
{
	/* TODO: make this debug error */
	ast_log(LOG_ERROR, "entered load_module\n");

        int8_t status;
        uint8_t c, hook_status;
        IFX_TAPI_TONE_t tone;
        IFX_TAPI_DEV_START_CFG_t tapistart;
        IFX_TAPI_MAP_DATA_t datamap;
        IFX_TAPI_ENC_CFG_t enc_cfg;
        IFX_TAPI_LINE_VOLUME_t line_vol;
        IFX_TAPI_WLEC_CFG_t lec_cfg;
        IFX_TAPI_JB_CFG_t jb_cfg;
        IFX_TAPI_CID_CFG_t cid_cfg;

        /* Open device */
        dev_ctx.dev_fd = tapi_dev_open(TAPI_LL_DEV_BASE_PATH, 0);

        if (dev_ctx.dev_fd < 0) {
                ast_log(LOG_ERROR, "tapi device open failed!\n");
                return TAPI_ERROR;
        }

        for (c = 0; c < TAPI_AUDIO_PORT_NUM; c++) {
		ch_fd[c] = dev_ctx.ch_fd[c] = tapi_dev_open(TAPI_LL_DEV_BASE_PATH, TAPI_AUDIO_PORT_NUM - c);

                if (dev_ctx.dev_fd < 0) {
                        ast_log(LOG_ERROR, "tapi channel%d open failed!\n", c);
                        return TAPI_ERROR;
                }
//                if (tapi_channel_revert)
//                        dev_ctx.data2phone_map[c] = c & 0x1 ? 1 : 0;
//                else
                        dev_ctx.data2phone_map[c] = c & 0x1 ? 0 : 1;
        }

        status = tapi_dev_firmware_download(dev_ctx.dev_fd, TAPI_LL_DEV_FIRMWARE_NAME);
        if (status != TAPI_OK) {
                ast_log(LOG_ERROR, "voice firmware download failed!\n");
                return TAPI_ERROR;
        }

	memset(&tapistart, 0x0, sizeof(IFX_TAPI_DEV_START_CFG_t));
	tapistart.nMode = IFX_TAPI_INIT_MODE_VOICE_CODER;

	/* Start TAPI */
	status = ioctl(dev_ctx.dev_fd, IFX_TAPI_DEV_START, &tapistart);
	if (status != TAPI_OK) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEV_START ioctl failed");
		return TAPI_ERROR;
	}

	for (c = 1; c < TAPI_AUDIO_PORT_NUM; c++) {
		memset(&tone, 0, sizeof(IFX_TAPI_TONE_t));
		status = ioctl(ch_fd[c], IFX_TAPI_TONE_TABLE_CFG_SET, &tone);
		if (status != TAPI_OK)
			 ast_log(LOG_ERROR, "IFX_TAPI_TONE_TABLE_CFG_SET %d failed!\n", c);
		/* Perform mapping */
		memset(&datamap, 0x0, sizeof(IFX_TAPI_MAP_DATA_t));
		datamap.nDstCh = dev_ctx.data2phone_map[c];
		datamap.nChType = IFX_TAPI_MAP_TYPE_PHONE;

		status = ioctl(dev_ctx.ch_fd[c], IFX_TAPI_MAP_DATA_ADD, &datamap);
		if (status != TAPI_OK) {
			ast_log(LOG_ERROR, "IFX_TAPI_MAP_DATA_ADD %d failed\n", c);
			return TAPI_ERROR;
		}

		/* Set Line feed */
		status = ioctl(dev_ctx.ch_fd[c], IFX_TAPI_LINE_FEED_SET, IFX_TAPI_LINE_FEED_STANDBY);
		if (status != TAPI_OK) {
			ast_log(LOG_ERROR, "IFX_TAPI_LINE_FEED_SET %d failed\n", c);
			return TAPI_ERROR;
		}

	}

        status = ioctl(ch_fd[0], IFX_TAPI_RING_START, 0);
        if (status != TAPI_OK) {
                ast_log(LOG_ERROR, "IFX_TAPI_RING_START 0 failed!\n");
//                return TAPI_ERROR;
        }

        status = ioctl(ch_fd[1], IFX_TAPI_RING_START, 0);
        if (status != TAPI_OK) {
                ast_log(LOG_ERROR, "IFX_TAPI_RING_START 1 failed!\n");
//               return TAPI_ERROR;
        }

	return 0;
}

static int unload_module(void)
{
	/* TODO: make this debug error */
	ast_log(LOG_ERROR, "entered unload_module\n");
	return 0;
}

AST_MODULE_INFO_STANDARD(ASTERISK_GPL_KEY, "Lantiq TAPI Channel");
