/*
 * Asterisk -- An open source telephony toolkit.
 *
 * Copyright (C) 2012, Luka Perkov
 * Copyright (C) 2012, John Crispin
 * Copyright (C) 2012, Kaspar Schleiser for T-Labs
 *                     (Deutsche Telekom Innovation Laboratories)
 *
 * Luka Perkov <openwrt@lukaperkov.net>
 * John Crispin <blogic@openwrt.org>
 * Andrej Vlašić <andrej.vlasic0@gmail.com>
 * Kaspar Schleiser <kaspar@schleiser.de>
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
 * \author Andrej Vlašić <andrej.vlasic0@gmail.com>
 * \author Kaspar Schleiser <kaspar@schleiser.de>
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

#define TAPI_LL_DEV_SELECT_TIMEOUT_MS	2000

#define TAPI_TONE_LOCALE_NONE                   0//32
#define TAPI_TONE_LOCALE_BUSY_CODE              27//33
#define TAPI_TONE_LOCALE_CONGESTION_CODE        27//34
#define TAPI_TONE_LOCALE_DIAL_CODE              25//35
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
#include "asterisk/sched.h"

#include "chan_phone.h"

#define IXJ_PHONE_RING_START(x)	ioctl(p->fd, PHONE_RING_START, &x);

#define DEFAULT_CALLER_ID "Unknown"
#define PHONE_MAX_BUF 480
#define DEFAULT_GAIN 0x0

static const char config[] = "tapi.conf";

/* Default context for dialtone mode */
static char context[AST_MAX_EXTENSION] = "default";

/* Default language */
static char language[MAX_LANGUAGE] = "";

static int echocancel = AEC_OFF;

static int silencesupression = 0;

static format_t prefformat = AST_FORMAT_G729A | AST_FORMAT_G723_1 | AST_FORMAT_SLINEAR | AST_FORMAT_ULAW;

static char firmware_filename[64] = "/lib/firmware/danube_firmware.bin";
static char bbd_filename[64] = "/lib/firmware/danube_bbd_fxs.bin";
static char base_path[64] = "/dev/vmmc";

/* Protect the interface list (of tapi_pvt's) */
AST_MUTEX_DEFINE_STATIC(iflock);

/* Protect the monitoring thread, so only one process can kill or start it, and not
   when it's doing something critical. */
AST_MUTEX_DEFINE_STATIC(monlock);

/* Boolean value whether the monitoring thread shall continue. */
static unsigned int monitor;

/* The scheduling thread */
struct ast_sched_thread *sched_thread;
   
/* This is the thread for the monitor which checks for input on the channels
   which are not currently in use.  */
static pthread_t monitor_thread = AST_PTHREADT_NULL;

static int restart_monitor(void);

/* The private structures of the Phone Jack channels are linked for
   selecting outgoing channels */

enum channel_state {
	ONHOOK,
	OFFHOOK,
	DIALING,
	INCALL,
	CALL_ENDED,
	RINGING,
	UNKNOWN
};

static const char * tapi_channel_state_string(enum channel_state state) {
	switch (state) {
		case ONHOOK: return "ONHOOK";
		case OFFHOOK: return "OFFHOOK";
		case DIALING: return "DIALING";
		case INCALL: return "INCALL";
		case CALL_ENDED: return "CALL_ENDED";
		case RINGING: return "RINGING";
		default: return "UNKNOWN";
	}
}

static struct tapi_pvt {
	struct ast_channel *owner;			/* Channel we belong to, possibly NULL 	*/
	struct tapi_pvt *next;				/* Next channel in list 				*/
	int port_id;						/* Physical port number of this object 	*/
	int channel_state;
	char *context;						/* this port's dialplan context			*/
	char ext[AST_MAX_EXTENSION+1];		/* the extension this port is connecting*/
	int dial_timer;						/* timer handle for autodial timeout	*/
	char dtmfbuf[AST_MAX_EXTENSION+1];	/* buffer holding dialed digits			*/
	int dtmfbuf_len;					/* lenght of dtmfbuf					*/
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

static struct tapi_pvt* tapi_get_next_pvt(struct tapi_pvt *p) {
	if (p->next)
		return p->next;
	else
		return NULL;
}


static struct tapi_pvt* tapi_get_cid_pvt(struct tapi_pvt *p, int port_id)
{
	while(p) {
		if (p->port_id == port_id) return p;
		p = tapi_get_next_pvt(p);
	}
	return NULL;
}

static void
tapi_start_ringing(int port) {
	ioctl(dev_ctx.ch_fd[port], IFX_TAPI_RING_START, 0);
}

static void
tapi_stop_ringing(int port) {
	ioctl(dev_ctx.ch_fd[port], IFX_TAPI_RING_STOP, 0);
}

static int
tapi_play_tone(int port, int tone) {
	if (ioctl(dev_ctx.ch_fd[port], IFX_TAPI_TONE_LOCAL_PLAY, tone)) {
		ast_log(LOG_ERROR, "IFX_TAPI_TONE_LOCAL_PLAY ioctl failed\n");
		return -1;
	}

	return 0;
}

static enum channel_state tapi_get_hookstatus(int port) {
	IFX_TAPI_LINE_HOOK_STATUS_GET_t status = 0;

	if (ioctl(dev_ctx.ch_fd[port], IFX_TAPI_LINE_HOOK_STATUS_GET, &status)) {
		ast_log(LOG_ERROR, "cannot get hookstate!\n");
        return UNKNOWN;
	}

	if (status) {
		return OFFHOOK;
	} else {
		return ONHOOK;
	}
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

	ast_mutex_lock(&iflock);
	
	struct tapi_pvt *pvt = ast->tech_pvt;
	
	ast_debug(1, "TAPI: phone_call() state: %s\n", tapi_channel_state_string(pvt->channel_state));

	if (pvt->channel_state == ONHOOK) {
		ast_debug(1, "TAPI: phone_call(): port %i ringing.\n", pvt->port_id);
		tapi_start_ringing(pvt->port_id);
		pvt->channel_state = RINGING;

		ast_setstate(ast, AST_STATE_RINGING);
		ast_queue_control(ast, AST_CONTROL_RINGING);

	} else {
		ast_debug(1, "TAPI: phone_call(): port %i busy.\n", pvt->port_id);
		ast_setstate(ast, AST_STATE_BUSY);
		ast_queue_control(ast, AST_CONTROL_BUSY);
	}
		
	ast_mutex_unlock(&iflock);

	return 0;
}

static int phone_hangup(struct ast_channel *ast)
{
	ast_debug(1, "TAPI: phone_hangup()\n");

	struct tapi_pvt *pvt = ast->tech_pvt;

	/* lock to prevent simultaneous access with do_monitor thread processing */
	ast_mutex_lock(&iflock);
	
	if (ast->_state == AST_STATE_RINGING) {
		ast_debug(1, "TAPI: phone_hangup(): ast->_state == AST_STATE_RINGING\n");
	}

	switch (pvt->channel_state) {
		case RINGING:
		case ONHOOK: 
			{
				tapi_stop_ringing(pvt->port_id);
				pvt->channel_state = ONHOOK;
				break;
			}
		default:
			{
				ast_debug(1, "TAPI: phone_hangup(): we were hung up, play busy tone.\n");
				pvt->channel_state = CALL_ENDED;
				tapi_play_tone(pvt->port_id, TAPI_TONE_LOCALE_BUSY_CODE);
			}
	}

	ast_setstate(ast, AST_STATE_DOWN);
	ast_module_unref(ast_module_info->self);
	ast->tech_pvt = NULL;
	pvt->owner = NULL;

	ast_mutex_unlock(&iflock);

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

static int go_onhook(int c) {
	int ret = -1;
	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_LINE_FEED_SET, IFX_TAPI_LINE_FEED_STANDBY)) {
		ast_log(LOG_ERROR, "IFX_TAPI_LINE_FEED_SET ioctl failed\n");
		goto out;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_ENC_STOP, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_ENC_STOP ioctl failed\n");
		goto out;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_DEC_STOP, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEC_STOP ioctl failed\n");
		goto out;
	}

	ret = tapi_play_tone(c, TAPI_TONE_LOCALE_NONE);

out:
	return ret;
}

static int end_dialing(int c) {
	ast_debug(1, "%s\n", __FUNCTION__);
	struct tapi_pvt *pvt = &iflist[c-1];

	if (pvt->dial_timer) {
		ast_sched_thread_del(sched_thread, pvt->dial_timer);
		pvt->dial_timer = 0;
	}

	if(pvt->owner) {
		ast_hangup(pvt->owner);
	}

	return 0;
}

static int end_call(int c) {
	ast_debug(1, "%s\n", __FUNCTION__);

	struct tapi_pvt *pvt = &iflist[c-1];
	
	if(pvt->owner) {
		ast_queue_hangup(pvt->owner);
	}

	return 0;
}

static int
tapi_dev_event_on_hook(int c)
{
	ast_log(LOG_ERROR, "TAPI: ONHOOK\n");

	if (ast_mutex_lock(&iflock)) {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		return -1;
	}
	
	int ret = 0;
	switch (iflist[c-1].channel_state) {
		case OFFHOOK: 
			{
				ret = go_onhook(c);
				break;
			}
		case DIALING: 
			{
				ret = end_dialing(c);
				break;
			}
		case INCALL: 
			{
				ret = end_call(c);
				break;
			}
		case CALL_ENDED:
			{
				ret = go_onhook(c);
				break;
			}
		default:
			{
				ret = -1;
				break;
			}
	}

	iflist[c-1].channel_state = ONHOOK;

	ast_mutex_unlock(&iflock);

	return ret;
}

static struct ast_channel *tapi_new(int state, int port_id, char *ext, char *ctx) {
	ast_debug(1, "tapi_new()\n");

	struct ast_channel *chan = NULL;

	struct tapi_pvt *pvt = &iflist[port_id-1];

	chan = ast_channel_alloc(1, state, NULL, NULL, "", ext, ctx, 0, port_id, "TAPI/%s", "1");

	chan->tech = &tapi_tech;
	chan->nativeformats = AST_FORMAT_ULAW;
	chan->readformat  = AST_FORMAT_ULAW;
	chan->writeformat = AST_FORMAT_ULAW;
	chan->tech_pvt = pvt;

	pvt->owner = chan;

	return chan;
}

static struct ast_channel *phone_requester(const char *type, format_t format, const struct ast_channel *requestor, void *data, int *cause) {
	char buf[256];
	
	struct ast_channel *chan = NULL;
	int port_id = -1;

	ast_debug(1, "Asked to create a TAPI channel with formats: %s\n", ast_getformatname_multiple(buf, sizeof(buf), format));

	if (ast_mutex_lock(&iflock)) {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		return NULL;
	}

	/* check for correct data argument */
	if (ast_strlen_zero(data)) {
		ast_log(LOG_ERROR, "Unable to create channel with empty destination.\n");
		*cause = AST_CAUSE_CHANNEL_UNACCEPTABLE;
		return NULL;
	}

	/* get our port number */
	port_id = atoi((char*) data);
	if (port_id < 1 || port_id > dev_ctx.channels) {
		ast_log(LOG_ERROR, "Unknown channel ID: \"%s\"\n", (char*) data);
		*cause = AST_CAUSE_CHANNEL_UNACCEPTABLE;
		return NULL;
	}

	chan = tapi_new(AST_STATE_DOWN, port_id, NULL, NULL);

	ast_mutex_unlock(&iflock);
	return chan;
}

static int
tapi_dev_event_off_hook(int c)
{
	ast_log(LOG_ERROR, "TAPI: OFFHOOK\n");

	if (ast_mutex_lock(&iflock)) {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		return -1;
	}
	
	iflist[c-1].channel_state = OFFHOOK;

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

	tapi_play_tone(c, TAPI_TONE_LOCALE_DIAL_CODE);

	ast_mutex_unlock(&iflock);

	return 0;
}

static void tapi_reset_dtmfbuf(struct tapi_pvt *pvt) {
		pvt->dtmfbuf[0] = '\0';
		pvt->dtmfbuf_len = 0;
		pvt->ext[0] = '\0';
}

static void tapi_dial(struct tapi_pvt *pvt) {
	ast_debug(1, "TAPI: tapi_dial()\n");

	struct ast_channel *chan = NULL;

	ast_debug(1, "TAPI: tapi_dial(): user want's to dial %s.\n", pvt->dtmfbuf);

	if (ast_exists_extension(NULL, pvt->context, pvt->dtmfbuf, 1, NULL)) {
		ast_debug(1, "TAPI: tapi_dial(): Asterisk knows extension %s, dialing.\n", pvt->dtmfbuf);

		strcpy(pvt->ext, pvt->dtmfbuf);

		ast_verbose( VERBOSE_PREFIX_3 "  extension exists, starting PBX %s\n", pvt->ext);

		chan = tapi_new(1, AST_STATE_UP, pvt->ext, pvt->context);
		chan->tech_pvt = pvt;
		pvt->owner = chan;

		strcpy(chan->exten, pvt->ext);
		ast_setstate(chan, AST_STATE_RING);
		pvt->channel_state = INCALL;

		if (ast_pbx_start(chan)) {
			ast_log(LOG_WARNING, "  Unable to start PBX on %s\n", chan->name);
			ast_hangup(chan);
		}
	}
	else {
		ast_debug(1, "TAPI: tapi_dial(): no extension found.\n");

		tapi_play_tone(pvt->port_id, TAPI_TONE_LOCALE_BUSY_CODE);
		pvt->channel_state = CALL_ENDED;
	}
	
	tapi_reset_dtmfbuf(pvt);
}

static int tapi_event_dial_timeout(const void* data) {
	ast_debug(1, "TAPI: tapi_event_dial_timeout()\n");

	struct tapi_pvt *pvt = (struct tapi_pvt *) data;
	pvt->dial_timer = 0;

	if (! pvt->channel_state == ONHOOK) {
		tapi_dial(pvt);
	} else {
		ast_debug(1, "TAPI: tapi_event_dial_timeout(): dial timeout in state ONHOOK.\n");
	}

	return 0;
}


static void tapi_dev_event_digit(int port, char digit) {
	ast_debug(1, "TAPI: tapi_event_digit() port=%i digit=%c\n", port, digit);
	if (ast_mutex_lock(&iflock)) {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		return;
	}

	struct tapi_pvt *pvt = &iflist[port-1];

	switch (pvt->channel_state) {
		case OFFHOOK:  
			pvt->channel_state = DIALING;
			
			tapi_play_tone(port, TAPI_TONE_LOCALE_NONE);

			/* fall through */
		case DIALING: 
			{
				if (digit == '#') {
					if (pvt->dial_timer) {
						ast_sched_thread_del(sched_thread, pvt->dial_timer);
						pvt->dial_timer = 0;
					}

					tapi_dial(pvt);
				} else {
					pvt->dtmfbuf[pvt->dtmfbuf_len] = digit;
					pvt->dtmfbuf_len++;
					pvt->dtmfbuf[pvt->dtmfbuf_len] = '\0';

					/* setup autodial timer */
					if (!pvt->dial_timer) {
						ast_debug(1, "TAPI: tapi_dev_event_digit() setting new timer.\n");
						pvt->dial_timer = ast_sched_thread_add(sched_thread, 2000, tapi_event_dial_timeout, (const void*) pvt);
					} else {
						ast_debug(1, "TAPI: tapi_dev_event_digit() replacing timer.\n");
						struct sched_context *sched = ast_sched_thread_get_context(sched_thread);
						AST_SCHED_REPLACE(pvt->dial_timer, sched, 2000, tapi_event_dial_timeout, (const void*) pvt);
					}
				}
				break;
			}
		default: {
					 ast_debug(1, "TAPI: tapi_dev_event_digit() unhandled state.\n");
					 break;
				 }
	}

	ast_mutex_unlock(&iflock);
	return;
}

static void
tapi_dev_event_handler(void)
{
	IFX_TAPI_EVENT_t event;
	unsigned int i;

	for (i = 0; i < dev_ctx.channels ; i++) {
	/*	if (ast_mutex_lock(&iflock)) {
			ast_log(LOG_WARNING, "Unable to lock the monitor\n");
			break;
		}*/

		memset (&event, 0, sizeof(event));
		event.ch = i;
		if (ioctl(dev_ctx.dev_fd, IFX_TAPI_EVENT_GET, &event))
			continue;
		if (event.id == IFX_TAPI_EVENT_NONE)
			continue;
/*
		ast_mutex_unlock(&iflock);
*/
		switch(event.id) {
			case IFX_TAPI_EVENT_FXS_ONHOOK:
				tapi_dev_event_on_hook(i);
				break;
			case IFX_TAPI_EVENT_FXS_OFFHOOK:
				tapi_dev_event_off_hook(i);
				break;
			case IFX_TAPI_EVENT_DTMF_DIGIT:
				ast_log(LOG_ERROR, "ON CHANNEL %d DETECTED DTMF DIGIT: %c\n", i, (char)event.data.dtmf.ascii);
				tapi_dev_event_digit(i, (char)event.data.dtmf.ascii);
				break;
			case IFX_TAPI_EVENT_PULSE_DIGIT:
				if (event.data.pulse.digit == 0xB) {
					ast_log(LOG_ERROR, "ON CHANNEL %d DETECTED PULSE DIGIT: %c\n", i, '0');
					tapi_dev_event_digit(i, '0');
				} else {
					ast_log(LOG_ERROR, "ON CHANNEL %d DETECTED PULSE DIGIT: %c\n", i, '0' + (char)event.data.pulse.digit);
					tapi_dev_event_digit(i, '0' + (char)event.data.pulse.digit);
				}
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

		if (poll(fds, dev_ctx.channels + 1, TAPI_LL_DEV_SELECT_TIMEOUT_MS) <= 0) {
			ast_mutex_unlock(&monlock);
			continue;
		}

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

static struct tapi_pvt *tapi_allocate_pvt(void) {
	struct tapi_pvt *tmp;

	tmp = ast_calloc(1, sizeof(*tmp));
	if (tmp) {
		tmp->owner = NULL;
		tmp->next = NULL;
		tmp->port_id       	= -1;
		tmp->channel_state 	= UNKNOWN;
		tmp->context		= strdup("default");;
		tmp->ext[0]			= '\0';
		tmp->dial_timer    	= 0;
		tmp->dtmfbuf[0]    	= '\0';
		tmp->dtmfbuf_len   	= 0;
	}

	return tmp;
}

static void tapi_create_pvts(struct tapi_pvt *p) {
	int i;
	struct tapi_pvt *tmp = p;
	struct tapi_pvt *tmp_next;

	for (i=0 ; i<dev_ctx.channels ; i++) {
		tmp_next = tapi_allocate_pvt();
		if (tmp != NULL) {
			tmp->next          = tmp_next;
			tmp_next->next     = NULL;
			tmp->port_id       = i;
		} else {
			iflist = tmp_next;
			tmp    = tmp_next;
			tmp->next = NULL;
		}
	}
}


static int load_module(void)
{
	struct ast_config *cfg;
	struct ast_variable *v;
	struct tapi_pvt *tmp;
	int txgain = DEFAULT_GAIN;
	int rxgain = DEFAULT_GAIN;
	int wlec_type = 0;
	int wlec_nlp = 0;
	int wlec_nbfe = 0;
	int wlec_nbne = 0;
	int wlec_wbne = 0;
	int jb_type = IFX_TAPI_JB_TYPE_ADAPTIVE;
	int jb_pckadpt = IFX_TAPI_JB_PKT_ADAPT_VOICE;
	int jb_localadpt = IFX_TAPI_JB_LOCAL_ADAPT_DEFAULT;
	int jb_scaling = 0x10;
	int jb_initialsize = 0x2d0;
	int jb_minsize = 0x50;
	int jb_maxsize = 0x5a0;
	int cid_type = IFX_TAPI_CID_STD_TELCORDIA;
	int vad_type = IFX_TAPI_ENC_VAD_NOVAD;
	dev_ctx.channels = TAPI_AUDIO_PORT_NUM_MAX;
	struct ast_flags config_flags = { 0 };
	
	if (!(sched_thread = ast_sched_thread_create())) {
		ast_log(LOG_ERROR, "Unable to create scheduler thread\n");
		return AST_MODULE_LOAD_FAILURE;
	}

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

	for (v = ast_variable_browse(cfg, "interfaces"); v; v = v->next) {
		if (!strcasecmp(v->name, "channels")) {
			dev_ctx.channels = atoi(v->value);
			if (!dev_ctx.channels) {
				ast_log(LOG_ERROR, "Invalid value for channels in config %s\n", config);
				ast_config_destroy(cfg);
				return AST_MODULE_LOAD_DECLINE;
			}
		} else if (!strcasecmp(v->name, "firmwarefilename")) {
			ast_copy_string(firmware_filename, v->value, sizeof(firmware_filename));
		} else if (!strcasecmp(v->name, "bbdfilename")) {
			ast_copy_string(bbd_filename, v->value, sizeof(bbd_filename));
		} else if (!strcasecmp(v->name, "basepath")) {
			ast_copy_string(base_path, v->value, sizeof(base_path));
		}
	}

	for (v = ast_variable_browse(cfg, "general"); v; v = v->next) {
		if (!strcasecmp(v->name, "rxgain")) {
			rxgain = atoi(v->value);
			if (!rxgain) {
				rxgain = DEFAULT_GAIN;
				ast_log(LOG_WARNING, "Invalid rxgain: %s, using default.\n", v->value);
			}
		} else if (!strcasecmp(v->name, "txgain")) {
			txgain = atoi(v->value);
			if (!txgain) {
				txgain = DEFAULT_GAIN;
				ast_log(LOG_WARNING, "Invalid txgain: %s, using default.\n", v->value);
			}
		} else if (!strcasecmp(v->name, "echocancel")) {
			if (!strcasecmp(v->value, "off")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_OFF;
			} else if (!strcasecmp(v->value, "nlec")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_NE;
				if (!strcasecmp(v->name, "echocancelfixedwindowsize")) {
					wlec_nbne = atoi(v->value);
				}
			} else if (!strcasecmp(v->value, "wlec")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_NFE;
				if (!strcasecmp(v->name, "echocancelnfemovingwindowsize")) {
					wlec_nbfe = atoi(v->value);
				} else if (!strcasecmp(v->name, "echocancelfixedwindowsize")) {
					wlec_nbne = atoi(v->value);
				} else if (!strcasecmp(v->name, "echocancelwidefixedwindowsize")) {
					wlec_wbne = atoi(v->value);
				}
			} else if (!strcasecmp(v->value, "nees")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_NE_ES;
			} else if (!strcasecmp(v->value, "nfees")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_NFE_ES;
			} else if (!strcasecmp(v->value, "es")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_ES;
			} else {
				wlec_type = IFX_TAPI_WLEC_TYPE_OFF;
				ast_log(LOG_ERROR, "Unknown echo cancellation type '%s'\n", v->value);
				ast_config_destroy(cfg);
				return AST_MODULE_LOAD_DECLINE;
			}
		} else if (!strcasecmp(v->name, "echocancelnlp")) {
			if (!strcasecmp(v->value, "on")) {
				wlec_nlp = IFX_TAPI_WLEC_NLP_ON;
			} else if (!strcasecmp(v->value, "off")) {
				wlec_nlp = IFX_TAPI_WLEC_NLP_OFF;
			} else {
				ast_log(LOG_ERROR, "Unknown echo cancellation nlp '%s'\n", v->value);
				ast_config_destroy(cfg);
				return AST_MODULE_LOAD_DECLINE;
			}
		} else if (!strcasecmp(v->name, "jitterbuffertype")) {
			if (!strcasecmp(v->value, "fixed")) {
				jb_type = IFX_TAPI_JB_TYPE_FIXED;
			} else if (!strcasecmp(v->value, "adaptive")) {
				jb_type = IFX_TAPI_JB_TYPE_ADAPTIVE;
				jb_localadpt = IFX_TAPI_JB_LOCAL_ADAPT_DEFAULT;
				if (!strcasecmp(v->name, "jitterbufferadaptation")) {
					if (!strcasecmp(v->value, "on")) {
						jb_localadpt = IFX_TAPI_JB_LOCAL_ADAPT_ON;
					} else if (!strcasecmp(v->value, "off")) {
						jb_localadpt = IFX_TAPI_JB_LOCAL_ADAPT_OFF;
					}
				} else if (!strcasecmp(v->name, "jitterbufferscalling")) {
					jb_scaling = atoi(v->value);
				} else if (!strcasecmp(v->name, "jitterbufferinitialsize")) {
					jb_initialsize = atoi(v->value);
				} else if (!strcasecmp(v->name, "jitterbufferminsize")) {
					jb_minsize = atoi(v->value);
				} else if (!strcasecmp(v->name, "jitterbuffermaxsize")) {
					jb_maxsize = atoi(v->value);
				}
			} else {
				ast_log(LOG_ERROR, "Unknown jitter buffer type '%s'\n", v->value);
				ast_config_destroy(cfg);
				return AST_MODULE_LOAD_DECLINE;
			}
		} else if (!strcasecmp(v->name, "jitterbufferpackettype")) {
			if (!strcasecmp(v->value, "voice")) {
				jb_pckadpt = IFX_TAPI_JB_PKT_ADAPT_VOICE;
			} else if (!strcasecmp(v->value, "data")) {
				jb_pckadpt = IFX_TAPI_JB_PKT_ADAPT_DATA;
			} else if (!strcasecmp(v->value, "datanorep")) {
				jb_pckadpt = IFX_TAPI_JB_PKT_ADAPT_DATA_NO_REP;
			} else {
				ast_log(LOG_ERROR, "Unknown jitter buffer packet adaptation type '%s'\n", v->value);
				ast_config_destroy(cfg);
				return AST_MODULE_LOAD_DECLINE;
			}
		} else if (!strcasecmp(v->name, "calleridtype")) {
			if (!strcasecmp(v->value, "telecordia")) {
				cid_type = IFX_TAPI_CID_STD_TELCORDIA;
			} else if (!strcasecmp(v->value, "etsifsk")) {
				cid_type = IFX_TAPI_CID_STD_ETSI_FSK;
			} else if (!strcasecmp(v->value, "etsidtmf")) {
				cid_type = IFX_TAPI_CID_STD_ETSI_DTMF;
			} else if (!strcasecmp(v->value, "sin")) {
				cid_type = IFX_TAPI_CID_STD_SIN;
			} else if (!strcasecmp(v->value, "ntt")) {
				cid_type = IFX_TAPI_CID_STD_NTT;
			} else if (!strcasecmp(v->value, "kpndtmf")) {
				cid_type = IFX_TAPI_CID_STD_KPN_DTMF;
			} else if (!strcasecmp(v->value, "kpndtmffsk")) {
				cid_type = IFX_TAPI_CID_STD_KPN_DTMF_FSK;
			} else {
				ast_log(LOG_ERROR, "Unknown caller id type '%s'\n", v->value);
				ast_config_destroy(cfg);
				return AST_MODULE_LOAD_DECLINE;
			}
		} else if (!strcasecmp(v->name, "voiceactivitydetection")) {
			if (!strcasecmp(v->value, "on")) {
				vad_type = IFX_TAPI_ENC_VAD_ON;
			} else if (!strcasecmp(v->value, "g711")) {
				vad_type = IFX_TAPI_ENC_VAD_G711;
			} else if (!strcasecmp(v->value, "cng")) {
				vad_type = IFX_TAPI_ENC_VAD_CNG_ONLY;
			} else if (!strcasecmp(v->value, "sc")) {
				vad_type = IFX_TAPI_ENC_VAD_SC_ONLY;
			} else {
				ast_log(LOG_ERROR, "Unknown voice activity detection value '%s'\n", v->value);
				ast_config_destroy(cfg);
				return AST_MODULE_LOAD_DECLINE;
			}
		}
	}

	tapi_create_pvts(iflist);

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
	IFX_TAPI_WLEC_CFG_t wlec_cfg;
	IFX_TAPI_JB_CFG_t jb_cfg;
	IFX_TAPI_CID_CFG_t cid_cfg;
	int32_t status;
	uint8_t c;

	/* open device */
	dev_ctx.dev_fd = tapi_dev_open(base_path, 0);

	if (dev_ctx.dev_fd < 0) {
		ast_log(LOG_ERROR, "tapi device open function failed\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	for (c = 0; c < dev_ctx.channels ; c++) {
		dev_ctx.ch_fd[c] = tapi_dev_open(base_path, c + 1);

		if (dev_ctx.ch_fd[c] < 0) {
			ast_log(LOG_ERROR, "tapi channel %d open function failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}
	}

	if (tapi_dev_firmware_download(dev_ctx.dev_fd, firmware_filename)) {
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

		/* ringing type */
		IFX_TAPI_RING_CFG_t ringingType;
		memset(&ringingType, 0, sizeof(IFX_TAPI_RING_CFG_t));
		ringingType.nMode = IFX_TAPI_RING_CFG_MODE_INTERNAL_BALANCED;
		ringingType.nSubmode = IFX_TAPI_RING_CFG_SUBMODE_DC_RNG_TRIP_FAST;
		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_RING_CFG_SET, (IFX_int32_t) &ringingType)) {
			ast_log(LOG_ERROR, "IFX_TAPI_RING_CFG_SET failed\n");
			return AST_MODULE_LOAD_FAILURE;
		}

		/* ring cadence */
		IFX_char_t data[15] = { 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
								0x00, 0x00, 0x00, 0x00, 0x00,     
								0x00, 0x00, 0x00, 0x00, 0x00 };

		IFX_TAPI_RING_CADENCE_t ringCadence;
		memset(&ringCadence, 0, sizeof(IFX_TAPI_RING_CADENCE_t));
		memcpy(&ringCadence.data, data, sizeof(data));
		ringCadence.nr = sizeof(data) * 8;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_RING_CADENCE_HR_SET, &ringCadence)) {
			ast_log(LOG_ERROR, "IFX_TAPI_RING_CADENCE_HR_SET failed\n");
			return AST_MODULE_LOAD_FAILURE;
		}

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

		/* Configure encoder for linear stream */
		memset(&enc_cfg, 0x0, sizeof(IFX_TAPI_ENC_CFG_t));
		enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_20;
		enc_cfg.nEncType = IFX_TAPI_COD_TYPE_LIN16_8;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_ENC_CFG_SET, &enc_cfg)) {
			ast_log(LOG_ERROR, "IFX_TAPI_ENC_CFG_SET %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}

		/* set volume */
		memset(&line_vol, 0, sizeof(line_vol));
		line_vol.nGainRx = rxgain;
		line_vol.nGainTx = txgain;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_PHONE_VOLUME_SET, &line_vol)) {
			ast_log(LOG_ERROR, "IFX_TAPI_PHONE_VOLUME_SET %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}

		/* Configure line echo canceller */
		memset(&wlec_cfg, 0, sizeof(wlec_cfg));
		wlec_cfg.nType = wlec_type;
		wlec_cfg.bNlp = wlec_nlp;
		wlec_cfg.nNBFEwindow = wlec_nbfe;
		wlec_cfg.nNBNEwindow = wlec_nbne;
		wlec_cfg.nWBNEwindow = wlec_wbne;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_WLEC_PHONE_CFG_SET, &wlec_cfg)) {
			ast_log(LOG_ERROR, "IFX_TAPI_WLEC_PHONE_CFG_SET %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}

		/* Configure jitter buffer */
		memset(&jb_cfg, 0, sizeof(jb_cfg));
		jb_cfg.nJbType = jb_type;
		jb_cfg.nPckAdpt = jb_pckadpt;
		jb_cfg.nLocalAdpt = jb_localadpt;
		jb_cfg.nScaling = jb_scaling;
		jb_cfg.nInitialSize = jb_initialsize;
		jb_cfg.nMinSize = jb_minsize;
		jb_cfg.nMaxSize = jb_maxsize;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_JB_CFG_SET, &jb_cfg)) {
			ast_log(LOG_ERROR, "IFX_TAPI_JB_CFG_SET %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}

		/* Configure Caller ID type */
		memset(&cid_cfg, 0, sizeof(cid_cfg));
		cid_cfg.nStandard = cid_type;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_CID_CFG_SET, &cid_cfg)) {
			ast_log(LOG_ERROR, "IIFX_TAPI_CID_CFG_SET %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}

		/* Configure voice activity detection */
		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_ENC_VAD_CFG_SET, vad_type)) {
			ast_log(LOG_ERROR, "IFX_TAPI_ENC_VAD_CFG_SET %d failed\n", c);
			return AST_MODULE_LOAD_FAILURE;
		}

		/* Set initial hook status */
		iflist[c-1].channel_state = tapi_get_hookstatus(c);
		
		if (iflist[c-1].channel_state == UNKNOWN) {
			return AST_MODULE_LOAD_FAILURE;
		}
	}

	restart_monitor();
	return AST_MODULE_LOAD_SUCCESS;
}

AST_MODULE_INFO_STANDARD(ASTERISK_GPL_KEY, "TAPI Telephony API Support");
