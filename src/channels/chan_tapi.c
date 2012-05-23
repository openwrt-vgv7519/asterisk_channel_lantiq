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
 */

/*! \file
 *
 * \brief TAPI Telephony Interface driver
 *
 * \author Luka Perkov <openwrt@lukaperkov.net>
 * \author John Crispin <blogic@openwrt.org>
 * 
 * \ingroup channel_drivers
 */

#include "asterisk.h"

ASTERISK_FILE_VERSION(__FILE__, "$Revision: xxx $")

#include <ctype.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <signal.h>
#ifdef HAVE_LINUX_COMPILER_H
#include <linux/compiler.h>
#endif
#include <linux/telephony.h>
/* Still use some IXJ specific stuff */
#include <linux/version.h>
#include <linux/ixjuser.h>

#include <drv_tapi/drv_tapi_io.h>
#include <drv_vmmc/vmmc_io.h>

#define TAPI_AUDIO_PORT_NUM_MAX		2
#define TAPI_LL_DEV_BASE_PATH		"/dev/vmmc"
#define TAPI_LL_DEV_FIRMWARE_NAME	"/lib/firmware/vr9_firmware.bin"
#define TAPI_LL_BBD_NAME		"/lib/firmware/vr9_bbd_fxs.bin"

#define TAPI_LL_DEV_SELECT_TIMEOUT_MS	2000

#define TAPI_TONE_LOCALE_NONE                   32
#define TAPI_TONE_LOCALE_BUSY_CODE              33
#define TAPI_TONE_LOCALE_CONGESTION_CODE        34
#define TAPI_TONE_LOCALE_DIAL_CODE              35
#define TAPI_TONE_LOCALE_RING_CODE              36
#define TAPI_TONE_LOCALE_WAITING_CODE           37

#include "asterisk/lock.h"
#include "asterisk/channel.h"
#include "asterisk/config.h"
#include "asterisk/module.h"
#include "asterisk/pbx.h"
#include "asterisk/utils.h"
#include "asterisk/callerid.h"
#include "asterisk/causes.h"
#include "asterisk/stringfields.h"
#include "asterisk/musiconhold.h"

#include "chan_phone.h"

#define IXJ_PHONE_RING_START(x)	ioctl(p->fd, PHONE_RING_START, &x);

#define DEFAULT_CALLER_ID "Unknown"
#define PHONE_MAX_BUF 480
#define DEFAULT_GAIN 0x100

static const char config[] = "tapi.conf";

/* Default context for dialtone mode */
static char context[AST_MAX_EXTENSION] = "default";

/* Default language */
static char language[MAX_LANGUAGE] = "";

static int echocancel = AEC_OFF;

static int silencesupression = 0;

static format_t prefformat = AST_FORMAT_G729A | AST_FORMAT_G723_1 | AST_FORMAT_SLINEAR | AST_FORMAT_ULAW;

/* Protect the interface list (of tapi_pvt's) */
AST_MUTEX_DEFINE_STATIC(iflock);

/* Protect the monitoring thread, so only one process can kill or start it, and not
   when it's doing something critical. */
AST_MUTEX_DEFINE_STATIC(monlock);

/* Boolean value whether the monitoring thread shall continue. */
static unsigned int monitor;
   
/* This is the thread for the monitor which checks for input on the channels
   which are not currently in use.  */
static pthread_t monitor_thread = AST_PTHREADT_NULL;

static int restart_monitor(void);

/* The private structures of the Phone Jack channels are linked for
   selecting outgoing channels */
   
#define MODE_DIALTONE 	1
#define MODE_IMMEDIATE	2
#define MODE_FXO	3
#define MODE_FXS        4
#define MODE_SIGMA      5

static struct tapi_pvt {
	struct ast_channel *owner;		/* Channel we belong to, possibly NULL */
	struct tapi_pvt *next;			/* Next channel in list */
} *iflist = NULL;

typedef struct
{
        int dev_fd;
        int channels;
        int ch_fd[TAPI_AUDIO_PORT_NUM_MAX];
} tapi_ctx;

tapi_ctx dev_ctx;

static char cid_num[AST_MAX_EXTENSION];
static char cid_name[AST_MAX_EXTENSION];

static int phone_digit_begin(struct ast_channel *ast, char digit);
static int phone_digit_end(struct ast_channel *ast, char digit, unsigned int duration);
static int phone_call(struct ast_channel *ast, char *dest, int timeout);
static int phone_hangup(struct ast_channel *ast);
static int phone_answer(struct ast_channel *ast);
static struct ast_frame *phone_read(struct ast_channel *ast);
static int phone_write(struct ast_channel *ast, struct ast_frame *frame);
static struct ast_frame *phone_exception(struct ast_channel *ast);
static int phone_send_text(struct ast_channel *ast, const char *text);
static int phone_fixup(struct ast_channel *old, struct ast_channel *new);
static int phone_indicate(struct ast_channel *chan, int condition, const void *data, size_t datalen);
static struct ast_channel *phone_requester(const char *type, format_t format, const struct ast_channel *requestor, void *data, int *cause);

static const struct ast_channel_tech tapi_tech = {
	.type = "TAPI",
	.description = "TAPI Telephony API Driver",
	.capabilities = AST_FORMAT_G723_1 | AST_FORMAT_SLINEAR | AST_FORMAT_ULAW | AST_FORMAT_G729A,
	.send_digit_begin = phone_digit_begin,
	.send_digit_end = phone_digit_end,
	.call = phone_call,
	.hangup = phone_hangup,
	.answer = phone_answer,
	.read = phone_read,
	.write = phone_write,
	.exception = phone_exception,
	.write_video = phone_write,
	.send_text = phone_send_text,
	.indicate = phone_indicate,
	.fixup = phone_fixup,
	.requester = phone_requester
};

static int
tapi_dev_open(const char *dev_path, const int32_t ch_num)
{
	char dev_name[FILENAME_MAX + 1];
	memset(dev_name, 0, sizeof(dev_name));
	snprintf(dev_name, FILENAME_MAX, "%s%u%u", dev_path, 1, ch_num);
	return open((const char*)dev_name, O_RDWR, 0644);
}

static int
tapi_dev_binary_buffer_create(const char *path, uint8_t **ppBuf, uint32_t *pBufSz)
{
	FILE *fd;
	struct stat file_stat;
	int32_t status = 0;

	fd = fopen(path, "rb");
	if (fd == NULL) {
		ast_log(LOG_ERROR, "binary file %s open failed\n", path);
		return -1;
	}

	if (stat(path, &file_stat)) {
		ast_log(LOG_ERROR, "file %s statistics get failed\n", path);
		return -1;
	}

	*ppBuf = malloc(file_stat.st_size);
	if (*ppBuf == NULL) {
		ast_log(LOG_ERROR, "binary file %s memory allocation failed\n", path);
		status = -1;
		goto on_exit;
	}

	if (fread (*ppBuf, sizeof(uint8_t), file_stat.st_size, fd) <= 0) {
		ast_log(LOG_ERROR, "file %s read failed\n", path);
		status = -1;
		goto on_exit;
	}

	*pBufSz = file_stat.st_size;

on_exit:
	if (fd != NULL)
		fclose(fd);

	if (*ppBuf != NULL && status)
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
	uint8_t *firmware = NULL;
	uint32_t size = 0;
	VMMC_IO_INIT vmmc_io_init;

	if (tapi_dev_binary_buffer_create(path, &firmware, &size)) {
		ast_log(LOG_ERROR, "binary buffer create failed!\n");
		return -1;
	}

	memset(&vmmc_io_init, 0, sizeof(VMMC_IO_INIT));
	vmmc_io_init.pPRAMfw = firmware;
	vmmc_io_init.pram_size = size;

	if (ioctl(fd, FIO_FW_DOWNLOAD, &vmmc_io_init)) {
		ast_log(LOG_ERROR, "FIO_FW_DOWNLOAD ioctl failed!\n");
		return -1;
	}

	tapi_dev_binary_buffer_delete(firmware);

	return 0;
}

static int phone_indicate(struct ast_channel *chan, int condition, const void *data, size_t datalen)
{
	ast_debug(1, "TAPI: phone_indicate()\n");
	return -1;
}

static int phone_fixup(struct ast_channel *old, struct ast_channel *new)
{
	ast_debug(1, "TAPI: phone_fixup()\n");
	return 0;
}

static int phone_digit_begin(struct ast_channel *chan, char digit)
{
	/* XXX Modify this callback to let Asterisk support controlling the length of DTMF */
	ast_debug(1, "TAPI: phone_digit_begin()\n");
	return 0;
}

static int phone_digit_end(struct ast_channel *ast, char digit, unsigned int duration)
{
	ast_debug(1, "TAPI: phone_digit_end()\n");
	return 0;
}

static int phone_call(struct ast_channel *ast, char *dest, int timeout)
{
	ast_debug(1, "TAPI: phone_call()\n");
	return 0;
}

static int phone_hangup(struct ast_channel *ast)
{
	ast_debug(1, "TAPI: phone_hangup()\n");
	return 0;
}

static int phone_setup(struct ast_channel *ast)
{
	ast_debug(1, "TAPI: phone_setup()\n");
	return 0;
}

static int phone_answer(struct ast_channel *ast)
{
	ast_debug(1, "TAPI: phone_answer()\n");
	return 0;
}

#if 0
static char phone_2digit(char c)
{
	if (c == 12)
		return '#';
	else if (c == 11)
		return '*';
	else if ((c < 10) && (c >= 0))
		return '0' + c - 1;
	else
		return '?';
}
#endif

static struct ast_frame  *phone_exception(struct ast_channel *ast)
{
	ast_debug(1, "TAPI: phone_exception()\n");
	return NULL;
}

static struct ast_frame  *phone_read(struct ast_channel *ast)
{
	ast_debug(1, "TAPI: phone_read()\n");
	return NULL;
}

static int phone_write_buf(struct tapi_pvt *p, const char *buf, int len, int frlen, int swap)
{
	ast_debug(1, "TAPI: phone_write_buf()\n");
	return -1;
}

static int phone_send_text(struct ast_channel *ast, const char *text)
{
	ast_debug(1, "TAPI: phone_send_text()\n");
	return -1;
}

static int phone_write(struct ast_channel *ast, struct ast_frame *frame)
{
	ast_debug(1, "TAPI: phone_write()\n");
	return -1;
}

static int
tapi_dev_event_on_hook(int c)
{
	ast_log(LOG_ERROR, "TAPI: ONHOOK\n");

	if (ast_mutex_lock(&iflock)) {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		return -1;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_LINE_FEED_SET, IFX_TAPI_LINE_FEED_STANDBY)) {
		ast_log(LOG_ERROR, "IFX_TAPI_LINE_FEED_SET ioctl failed\n");
		return -1;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_ENC_STOP, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_ENC_STOP ioctl failed\n");
		return -1;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_DEC_STOP, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEC_STOP ioctl failed\n");
		return -1;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_TONE_LOCAL_PLAY, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_TONE_LOCAL_PLAY ioctl failed\n");
		return -1;
	}

	ast_mutex_unlock(&iflock);

	return 0;
}

static struct ast_channel *phone_requester(const char *type, format_t format, const struct ast_channel *requestor, void *data, int *cause) {
	ast_debug(1, "TAPI: phone_requester()\n");
	return NULL;
}

static int
tapi_dev_event_off_hook(int c)
{
	ast_log(LOG_ERROR, "TAPI: OFFHOOK\n");

	if (ast_mutex_lock(&iflock)) {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		return -1;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_LINE_FEED_SET, IFX_TAPI_LINE_FEED_ACTIVE)) {
		ast_log(LOG_ERROR, "IFX_TAPI_LINE_FEED_SET ioctl failed\n");
		return -1;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_ENC_START, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_ENC_START ioctl failed\n");
		return -1;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_DEC_START, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEC_START ioctl failed\n");
		return -1;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_TONE_LOCAL_PLAY, 25)) {
		ast_log(LOG_ERROR, "IFX_TAPI_TONE_LOCAL_PLAY ioctl failed\n");
		return -1;
	}

	ast_mutex_unlock(&iflock);

	return 0;
}

static void
tapi_dev_event_handler()
{
	IFX_TAPI_EVENT_t event;
	unsigned int i;

	for (i = 0; i < dev_ctx.channels ; i++) {
		if (ast_mutex_lock(&iflock)) {
			ast_log(LOG_WARNING, "Unable to lock the monitor\n");
			break;
		}

		memset (&event, 0, sizeof(event));
		event.ch = i;
		if (ioctl(dev_ctx.dev_fd, IFX_TAPI_EVENT_GET, &event))
			continue;
		if (event.id == IFX_TAPI_EVENT_NONE)
			continue;

		ast_mutex_unlock(&iflock);

		switch(event.id) {
			case IFX_TAPI_EVENT_FXS_ONHOOK:
				tapi_dev_event_on_hook(i);
				break;
			case IFX_TAPI_EVENT_FXS_OFFHOOK:
				tapi_dev_event_off_hook(i);
				break;
			case IFX_TAPI_EVENT_DTMF_DIGIT:
				ast_log(LOG_ERROR, "ON CHANNEL %d DETECTED DIGIT: %c\n", i, (char)event.data.dtmf.ascii);
				break;
			case IFX_TAPI_EVENT_COD_DEC_CHG:
			case IFX_TAPI_EVENT_TONE_GEN_END:
			case IFX_TAPI_EVENT_CID_TX_SEQ_END:
				break;
			default:
				ast_log(LOG_ERROR, "Unable TAPI event %08X\n", event.id);
				break;
		}
	}
}

static void *
tapi_events_monitor(void *data)
{
	ast_verbose("TAPI thread started\n");

	struct pollfd fds[3];

	fds[0].fd = dev_ctx.dev_fd;
	fds[0].events = POLLIN;
#ifdef SKIP_DATA_HANDLER
	fds[1].fd = dev_ctx.ch_fd[0];
	fds[1].events = POLLIN;
	fds[2].fd = dev_ctx.ch_fd[1];
	fds[2].events = POLLIN;
#endif

	while (monitor) {
		if (ast_mutex_lock(&monlock)) {
			ast_log(LOG_WARNING, "Unable to lock the monitor\n");
			break;
		}

		if (poll(fds, dev_ctx.channels + 1, TAPI_LL_DEV_SELECT_TIMEOUT_MS) <= 0)
			continue;

		if (fds[0].revents == POLLIN) {
			tapi_dev_event_handler();
		}

		ast_mutex_unlock(&monlock);

#ifdef SKIP_DATA_HANDLER
		if (fds[1].revents == POLLIN) {
			if (tapi_dev_data_handler(&streams[0])) {
				ast_verbose("TAPI: data handler failed\n");
				break;
			}
		}

		if (fds[2].revents == POLLIN) {
			if (tapi_dev_data_handler(&streams[1])) {
				ast_verbose("TAPI: data handler failed\n");
				break;
			}
		}
#endif
	}

	return NULL;
}

static int restart_monitor()
{
	/* If we're supposed to be stopped -- stay stopped */
	if (monitor_thread == AST_PTHREADT_STOP)
		return 0;
	if (ast_mutex_lock(&monlock)) {
		ast_log(LOG_WARNING, "Unable to lock monitor\n");
		return -1;
	}
	if (monitor_thread == pthread_self()) {
		ast_mutex_unlock(&monlock);
		ast_log(LOG_WARNING, "Cannot kill myself\n");
		return -1;
	}
	if (monitor_thread != AST_PTHREADT_NULL) {
		if (ast_mutex_lock(&iflock)) {
			ast_mutex_unlock(&monlock);
			ast_log(LOG_WARNING, "Unable to lock the interface list\n");
			return -1;
		}
		monitor = 0;
		while (pthread_kill(monitor_thread, SIGURG) == 0)
			sched_yield();
		pthread_join(monitor_thread, NULL);
		ast_mutex_unlock(&iflock);
	}
	monitor = 1;
	/* Start a new monitor */
	if (ast_pthread_create_background(&monitor_thread, NULL, tapi_events_monitor, NULL) < 0) {
		ast_mutex_unlock(&monlock);
		ast_log(LOG_ERROR, "Unable to start monitor thread.\n");
		return -1;
	}
	ast_mutex_unlock(&monlock);
	return 0;
}

static int unload_module(void)
{
	int c;

	ast_channel_unregister(&tapi_tech);

	if (!ast_mutex_lock(&iflock)) {
//		for (c = 0; c < dev_ctx.channels ; c++)
//			ast_softhangup(p->owner, AST_SOFTHANGUP_APPUNLOAD);
		ast_mutex_unlock(&iflock);
	} else {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		return -1;
	}

	if (!ast_mutex_lock(&monlock)) {
		if (monitor_thread > AST_PTHREADT_NULL) {
			monitor = 0;
			while (pthread_kill(monitor_thread, SIGURG) == 0)
				sched_yield();
			pthread_join(monitor_thread, NULL);
		}
		monitor_thread = AST_PTHREADT_STOP;
		ast_mutex_unlock(&monlock);
	} else {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		return -1;
	}

	if (!ast_mutex_lock(&iflock)) {
		if (ioctl(dev_ctx.dev_fd, IFX_TAPI_DEV_STOP, 0)) {
			ast_log(LOG_WARNING, "IFX_TAPI_DEV_STOP ioctl failed\n");
		}

		close(dev_ctx.dev_fd);
		for (c = 0; c < dev_ctx.channels ; c++) close(dev_ctx.ch_fd[c]);

		ast_mutex_unlock(&iflock);
	} else {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		return -1;
	}
		
	return 0;
}

static int load_module(void)
{
	struct ast_config *cfg;
	struct ast_variable *v;
	struct tapi_pvt *tmp;
	int txgain = DEFAULT_GAIN, rxgain = DEFAULT_GAIN; /* default gain 1.0 */
	struct ast_flags config_flags = { 0 };

	if ((cfg = ast_config_load(config, config_flags)) == CONFIG_STATUS_FILEINVALID) {
		ast_log(LOG_ERROR, "Config file %s is in an invalid format.  Aborting.\n", config);
		return AST_MODULE_LOAD_DECLINE;
	}

	/* We *must* have a config file otherwise stop immediately */
	if (!cfg) {
		ast_log(LOG_ERROR, "Unable to load config %s\n", config);
		return AST_MODULE_LOAD_DECLINE;
	}

	if (ast_mutex_lock(&iflock)) {
		ast_log(LOG_ERROR, "Unable to lock interface list.\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	dev_ctx.channels = TAPI_AUDIO_PORT_NUM_MAX;
	for (v = ast_variable_browse(cfg, "interfaces"); v; v = v->next) {
		if (!strcasecmp(v->name, "channels")) {
			dev_ctx.channels = atoi(v->value);
			if (!dev_ctx.channels) {
				ast_log(LOG_ERROR, "Invalid value for channels in config %s\n", config);
				ast_config_destroy(cfg);
				return AST_MODULE_LOAD_DECLINE;
			}
		}
	}
	ast_mutex_unlock(&iflock);

	if (ast_channel_register(&tapi_tech)) {
		ast_log(LOG_ERROR, "Unable to register channel class 'Phone'\n");
		ast_config_destroy(cfg);
		unload_module();
		return AST_MODULE_LOAD_FAILURE;
	}
	ast_config_destroy(cfg);
	
	/* tapi */
	IFX_TAPI_TONE_t tone;
	IFX_TAPI_DEV_START_CFG_t dev_start;
	IFX_TAPI_MAP_DATA_t map_data;
	IFX_TAPI_ENC_CFG_t enc_cfg;
	IFX_TAPI_LINE_VOLUME_t line_vol;
	IFX_TAPI_WLEC_CFG_t lec_cfg;
	IFX_TAPI_JB_CFG_t jb_cfg;
	IFX_TAPI_CID_CFG_t cid_cfg;
	int32_t status;
	uint8_t c;

	/* open device */
	dev_ctx.dev_fd = tapi_dev_open(TAPI_LL_DEV_BASE_PATH, 0);

	if (dev_ctx.dev_fd < 0) {
		ast_log(LOG_ERROR, "tapi device open function failed\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	for (c = 0; c < dev_ctx.channels ; c++) {
		dev_ctx.ch_fd[c] = tapi_dev_open(TAPI_LL_DEV_BASE_PATH, c + 1);

		if (dev_ctx.ch_fd[c] < 0) {
			ast_log(LOG_ERROR, "tapi channel %d open function failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}
	}

	if (tapi_dev_firmware_download(dev_ctx.dev_fd, TAPI_LL_DEV_FIRMWARE_NAME)) {
		ast_log(LOG_ERROR, "voice firmware download failed\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	if (ioctl(dev_ctx.dev_fd, IFX_TAPI_DEV_STOP, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEV_STOP ioctl failed\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	memset(&dev_start, 0x0, sizeof(IFX_TAPI_DEV_START_CFG_t));
	dev_start.nMode = IFX_TAPI_INIT_MODE_VOICE_CODER;

	/* Start TAPI */
	if (ioctl(dev_ctx.dev_fd, IFX_TAPI_DEV_START, &dev_start)) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEV_START ioctl failed\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	/* tones */
	memset(&tone, 0, sizeof(IFX_TAPI_TONE_t));
	for (c = 0; c < dev_ctx.channels ; c++) {
#ifdef TODO
		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_TONE_TABLE_CFG_SET, &tone)) {
			ast_log(LOG_ERROR, "IFX_TAPI_TONE_TABLE_CFG_SET %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}
#endif

		/* perform mapping */
#ifdef DONT_KNOW_IF_NEEDED
		memset(&map_data, 0x0, sizeof(IFX_TAPI_MAP_DATA_t));
		map_data.nDstCh = c;
		map_data.nChType = IFX_TAPI_MAP_TYPE_PHONE;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_MAP_DATA_REMOVE, &map_data)) {
			ast_log(LOG_ERROR, "IFX_TAPI_MAP_DATA_REMOVE %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}
#endif

		memset(&map_data, 0x0, sizeof(IFX_TAPI_MAP_DATA_t));
		map_data.nDstCh = c;
		map_data.nChType = IFX_TAPI_MAP_TYPE_PHONE;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_MAP_DATA_ADD, &map_data)) {
			ast_log(LOG_ERROR, "IFX_TAPI_MAP_DATA_ADD %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}

		/* set line feed */
		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_LINE_FEED_SET, IFX_TAPI_LINE_FEED_STANDBY)) {
			ast_log(LOG_ERROR, "IFX_TAPI_LINE_FEED_SET %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}
	}

	restart_monitor();
	return AST_MODULE_LOAD_SUCCESS;
}

AST_MODULE_INFO_STANDARD(ASTERISK_GPL_KEY, "TAPI Telephony API Support");
