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
	int fd;							/* Raw file descriptor for this device */
	struct ast_channel *owner;		/* Channel we belong to, possibly NULL */
	int mode;						/* Is this in the  */
	format_t lastformat;            /* Last output format */
	format_t lastinput;             /* Last input format */
	int ministate;					/* Miniature state, for dialtone mode */
	char dev[256];					/* Device name */
	struct tapi_pvt *next;			/* Next channel in list */
	struct ast_frame fr;			/* Frame */
	char offset[AST_FRIENDLY_OFFSET];
	char buf[PHONE_MAX_BUF];					/* Static buffer for reading frames */
	int obuflen;
	int dialtone;
	int txgain, rxgain;             /* gain control for playing, recording  */
									/* 0x100 - 1.0, 0x200 - 2.0, 0x80 - 0.5 */
	int cpt;						/* Call Progress Tone playing? */
	int silencesupression;
	char context[AST_MAX_EXTENSION];
	char obuf[PHONE_MAX_BUF * 2];
	char ext[AST_MAX_EXTENSION];
	char language[MAX_LANGUAGE];
	char cid_num[AST_MAX_EXTENSION];
	char cid_name[AST_MAX_EXTENSION];
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
	.fixup = phone_fixup
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
	struct tapi_pvt *p = chan->tech_pvt;
	int res=-1;
	ast_debug(1, "Requested indication %d on channel %s\n", condition, chan->name);
	switch(condition) {
	case AST_CONTROL_FLASH:
		ioctl(p->fd, IXJCTL_PSTN_SET_STATE, PSTN_ON_HOOK);
		usleep(320000);
		ioctl(p->fd, IXJCTL_PSTN_SET_STATE, PSTN_OFF_HOOK);
			p->lastformat = -1;
			res = 0;
			break;
	case AST_CONTROL_HOLD:
		ast_moh_start(chan, data, NULL);
		break;
	case AST_CONTROL_UNHOLD:
		ast_moh_stop(chan);
		break;
	case AST_CONTROL_SRCUPDATE:
		res = 0;
		break;
	default:
		ast_log(LOG_WARNING, "Condition %d is not supported on channel %s\n", condition, chan->name);
	}
	return res;
}

static int phone_fixup(struct ast_channel *old, struct ast_channel *new)
{
	struct tapi_pvt *pvt = old->tech_pvt;
	if (pvt && pvt->owner == old)
		pvt->owner = new;
	return 0;
}

static int phone_digit_begin(struct ast_channel *chan, char digit)
{
	/* XXX Modify this callback to let Asterisk support controlling the length of DTMF */
	return 0;
}

static int phone_digit_end(struct ast_channel *ast, char digit, unsigned int duration)
{
	struct tapi_pvt *p;
	int outdigit;
	p = ast->tech_pvt;
	ast_debug(1, "Dialed %c\n", digit);
	switch(digit) {
	case '0':
	case '1':
	case '2':
	case '3':
	case '4':
	case '5':
	case '6':
	case '7':
	case '8':
	case '9':
		outdigit = digit - '0';
		break;
	case '*':
		outdigit = 11;
		break;
	case '#':
		outdigit = 12;
		break;
	case 'f':	/*flash*/
	case 'F':
		ioctl(p->fd, IXJCTL_PSTN_SET_STATE, PSTN_ON_HOOK);
		usleep(320000);
		ioctl(p->fd, IXJCTL_PSTN_SET_STATE, PSTN_OFF_HOOK);
		p->lastformat = -1;
		return 0;
	default:
		ast_log(LOG_WARNING, "Unknown digit '%c'\n", digit);
		return -1;
	}
	ast_debug(1, "Dialed %d\n", outdigit);
	ioctl(p->fd, PHONE_PLAY_TONE, outdigit);
	p->lastformat = -1;
	return 0;
}

static int phone_call(struct ast_channel *ast, char *dest, int timeout)
{
	struct tapi_pvt *p;

	PHONE_CID cid;
	struct timeval UtcTime = ast_tvnow();
	struct ast_tm tm;
	int start;

	ast_localtime(&UtcTime, &tm, NULL);

	memset(&cid, 0, sizeof(PHONE_CID));
    snprintf(cid.month, sizeof(cid.month), "%02d",(tm.tm_mon + 1));
    snprintf(cid.day, sizeof(cid.day),     "%02d", tm.tm_mday);
    snprintf(cid.hour, sizeof(cid.hour),   "%02d", tm.tm_hour);
    snprintf(cid.min, sizeof(cid.min),     "%02d", tm.tm_min);
	/* the standard format of ast->callerid is:  "name" <number>, but not always complete */
	if (!ast->connected.id.name.valid
		|| ast_strlen_zero(ast->connected.id.name.str)) {
		strcpy(cid.name, DEFAULT_CALLER_ID);
	} else {
		ast_copy_string(cid.name, ast->connected.id.name.str, sizeof(cid.name));
	}

	if (ast->connected.id.number.valid && ast->connected.id.number.str) {
		ast_copy_string(cid.number, ast->connected.id.number.str, sizeof(cid.number));
	}

	p = ast->tech_pvt;

	if ((ast->_state != AST_STATE_DOWN) && (ast->_state != AST_STATE_RESERVED)) {
		ast_log(LOG_WARNING, "phone_call called on %s, neither down nor reserved\n", ast->name);
		return -1;
	}
	ast_debug(1, "Ringing %s on %s (%d)\n", dest, ast->name, ast->fds[0]);

	start = IXJ_PHONE_RING_START(cid);
	if (start == -1)
		return -1;
	
	if (p->mode == MODE_FXS) {
		char *digit = strchr(dest, '/');
		if (digit)
		{
		  digit++;
		  while (*digit)
		    phone_digit_end(ast, *digit++, 0);
		}
	}
 
  	ast_setstate(ast, AST_STATE_RINGING);
	ast_queue_control(ast, AST_CONTROL_RINGING);
	return 0;
}

static int phone_hangup(struct ast_channel *ast)
{
	struct tapi_pvt *p;
	p = ast->tech_pvt;
	ast_debug(1, "phone_hangup(%s)\n", ast->name);
	if (!ast->tech_pvt) {
		ast_log(LOG_WARNING, "Asked to hangup channel not connected\n");
		return 0;
	}
	/* XXX Is there anything we can do to really hang up except stop recording? */
	ast_setstate(ast, AST_STATE_DOWN);
	if (ioctl(p->fd, PHONE_REC_STOP))
		ast_log(LOG_WARNING, "Failed to stop recording\n");
	if (ioctl(p->fd, PHONE_PLAY_STOP))
		ast_log(LOG_WARNING, "Failed to stop playing\n");
	if (ioctl(p->fd, PHONE_RING_STOP))
		ast_log(LOG_WARNING, "Failed to stop ringing\n");
	if (ioctl(p->fd, PHONE_CPT_STOP))
		ast_log(LOG_WARNING, "Failed to stop sounds\n");

	/* If it's an FXO, hang them up */
	if (p->mode == MODE_FXO) {
		if (ioctl(p->fd, PHONE_PSTN_SET_STATE, PSTN_ON_HOOK))
			ast_debug(1, "ioctl(PHONE_PSTN_SET_STATE) failed on %s (%s)\n",ast->name, strerror(errno));
	}

	/* If they're off hook, give a busy signal */
	if (ioctl(p->fd, PHONE_HOOKSTATE)) {
		ast_debug(1, "Got hunghup, giving busy signal\n");
		ioctl(p->fd, PHONE_BUSY);
		p->cpt = 1;
	}
	p->lastformat = -1;
	p->lastinput = -1;
	p->ministate = 0;
	p->obuflen = 0;
	p->dialtone = 0;
	memset(p->ext, 0, sizeof(p->ext));
	((struct tapi_pvt *)(ast->tech_pvt))->owner = NULL;
	ast_module_unref(ast_module_info->self);
	ast_verb(3, "Hungup '%s'\n", ast->name);
	ast->tech_pvt = NULL;
	ast_setstate(ast, AST_STATE_DOWN);
	restart_monitor();
	return 0;
}

static int phone_setup(struct ast_channel *ast)
{
	struct tapi_pvt *p;
	p = ast->tech_pvt;
	ioctl(p->fd, PHONE_CPT_STOP);
	/* Nothing to answering really, just start recording */
	if (ast->rawreadformat == AST_FORMAT_G729A) {
		/* Prefer g729 */
		ioctl(p->fd, PHONE_REC_STOP);
		if (p->lastinput != AST_FORMAT_G729A) {
			p->lastinput = AST_FORMAT_G729A;
			if (ioctl(p->fd, PHONE_REC_CODEC, G729)) {
				ast_log(LOG_WARNING, "Failed to set codec to g729\n");
				return -1;
			}
		}
        } else if (ast->rawreadformat == AST_FORMAT_G723_1) {
		ioctl(p->fd, PHONE_REC_STOP);
		if (p->lastinput != AST_FORMAT_G723_1) {
			p->lastinput = AST_FORMAT_G723_1;
			if (ioctl(p->fd, PHONE_REC_CODEC, G723_63)) {
				ast_log(LOG_WARNING, "Failed to set codec to g723.1\n");
				return -1;
			}
		}
	} else if (ast->rawreadformat == AST_FORMAT_SLINEAR) {
		ioctl(p->fd, PHONE_REC_STOP);
		if (p->lastinput != AST_FORMAT_SLINEAR) {
			p->lastinput = AST_FORMAT_SLINEAR;
			if (ioctl(p->fd, PHONE_REC_CODEC, LINEAR16)) {
				ast_log(LOG_WARNING, "Failed to set codec to signed linear 16\n");
				return -1;
			}
		}
	} else if (ast->rawreadformat == AST_FORMAT_ULAW) {
		ioctl(p->fd, PHONE_REC_STOP);
		if (p->lastinput != AST_FORMAT_ULAW) {
			p->lastinput = AST_FORMAT_ULAW;
			if (ioctl(p->fd, PHONE_REC_CODEC, ULAW)) {
				ast_log(LOG_WARNING, "Failed to set codec to uLaw\n");
				return -1;
			}
		}
	} else if (p->mode == MODE_FXS) {
		ioctl(p->fd, PHONE_REC_STOP);
		if (p->lastinput != ast->rawreadformat) {
			p->lastinput = ast->rawreadformat;
			if (ioctl(p->fd, PHONE_REC_CODEC, ast->rawreadformat)) {
				ast_log(LOG_WARNING, "Failed to set codec to %s\n", 
					ast_getformatname(ast->rawreadformat));
				return -1;
			}
		}
	} else {
		ast_log(LOG_WARNING, "Can't do format %s\n", ast_getformatname(ast->rawreadformat));
		return -1;
	}
	if (ioctl(p->fd, PHONE_REC_START)) {
		ast_log(LOG_WARNING, "Failed to start recording\n");
		return -1;
	}
	/* set the DTMF times (the default is too short) */
	ioctl(p->fd, PHONE_SET_TONE_ON_TIME, 300);
	ioctl(p->fd, PHONE_SET_TONE_OFF_TIME, 200);
	return 0;
}

static int phone_answer(struct ast_channel *ast)
{
	struct tapi_pvt *p;
	p = ast->tech_pvt;
	/* In case it's a LineJack, take it off hook */
	if (p->mode == MODE_FXO) {
		if (ioctl(p->fd, PHONE_PSTN_SET_STATE, PSTN_OFF_HOOK))
			ast_debug(1, "ioctl(PHONE_PSTN_SET_STATE) failed on %s (%s)\n", ast->name, strerror(errno));
		else
			ast_debug(1, "Took linejack off hook\n");
	}
	phone_setup(ast);
	ast_debug(1, "phone_answer(%s)\n", ast->name);
	ast->rings = 0;
	ast_setstate(ast, AST_STATE_UP);
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
	int res;
	union telephony_exception phonee;
	struct tapi_pvt *p = ast->tech_pvt;
	char digit;

	/* Some nice norms */
	p->fr.datalen = 0;
	p->fr.samples = 0;
	p->fr.data.ptr =  NULL;
	p->fr.src = "Phone";
	p->fr.offset = 0;
	p->fr.mallocd=0;
	p->fr.delivery = ast_tv(0,0);
	
	phonee.bytes = ioctl(p->fd, PHONE_EXCEPTION);
	if (phonee.bits.dtmf_ready)  {
		ast_debug(1, "phone_exception(): DTMF\n");
	
		/* We've got a digit -- Just handle this nicely and easily */
		digit =  ioctl(p->fd, PHONE_GET_DTMF_ASCII);
		p->fr.subclass.integer = digit;
		p->fr.frametype = AST_FRAME_DTMF;
		return &p->fr;
	}
	if (phonee.bits.hookstate) {
		ast_debug(1, "Hookstate changed\n");
		res = ioctl(p->fd, PHONE_HOOKSTATE);
		/* See if we've gone on hook, if so, notify by returning NULL */
		ast_debug(1, "New hookstate: %d\n", res);
		if (!res && (p->mode != MODE_FXO))
			return NULL;
		else {
			if (ast->_state == AST_STATE_RINGING) {
				/* They've picked up the phone */
				p->fr.frametype = AST_FRAME_CONTROL;
				p->fr.subclass.integer = AST_CONTROL_ANSWER;
				phone_setup(ast);
				ast_setstate(ast, AST_STATE_UP);
				return &p->fr;
			}  else 
				ast_log(LOG_WARNING, "Got off hook in weird state %d\n", ast->_state);
		}
	}
#if 1
	if (phonee.bits.pstn_ring)
		ast_verbose("Unit is ringing\n");
	if (phonee.bits.caller_id) {
		ast_verbose("We have caller ID\n");
	}
	if (phonee.bits.pstn_wink)
		ast_verbose("Detected Wink\n");
#endif
	/* Strange -- nothing there.. */
	p->fr.frametype = AST_FRAME_NULL;
	p->fr.subclass.integer = 0;
	return &p->fr;
}

static struct ast_frame  *phone_read(struct ast_channel *ast)
{
	int res;
	struct tapi_pvt *p = ast->tech_pvt;
	

	/* Some nice norms */
	p->fr.datalen = 0;
	p->fr.samples = 0;
	p->fr.data.ptr =  NULL;
	p->fr.src = "Phone";
	p->fr.offset = 0;
	p->fr.mallocd=0;
	p->fr.delivery = ast_tv(0,0);

	/* Try to read some data... */
	CHECK_BLOCKING(ast);
	res = read(p->fd, p->buf, PHONE_MAX_BUF);
	ast_clear_flag(ast, AST_FLAG_BLOCKING);
	if (res < 0) {
#if 0
		if (errno == EAGAIN) {
			ast_log(LOG_WARNING, "Null frame received\n");
			p->fr.frametype = AST_FRAME_NULL;
			p->fr.subclass = 0;
			return &p->fr;
		}
#endif
		ast_log(LOG_WARNING, "Error reading: %s\n", strerror(errno));
		return NULL;
	}
	p->fr.data.ptr = p->buf;
	if (p->mode != MODE_FXS)
	switch(p->buf[0] & 0x3) {
	case '0':
	case '1':
		/* Normal */
		break;
	case '2':
	case '3':
		/* VAD/CNG, only send two words */
		res = 4;
		break;
	}
	p->fr.samples = 240;
	p->fr.datalen = res;
	p->fr.frametype = p->lastinput <= AST_FORMAT_AUDIO_MASK ?
                          AST_FRAME_VOICE : 
			  p->lastinput <= AST_FORMAT_PNG ? AST_FRAME_IMAGE 
			  : AST_FRAME_VIDEO;
	p->fr.subclass.codec = p->lastinput;
	p->fr.offset = AST_FRIENDLY_OFFSET;
	/* Byteswap from little-endian to native-endian */
	if (p->fr.subclass.codec == AST_FORMAT_SLINEAR)
		ast_frame_byteswap_le(&p->fr);
	return &p->fr;
}

static int phone_write_buf(struct tapi_pvt *p, const char *buf, int len, int frlen, int swap)
{
	int res;
	/* Store as much of the buffer as we can, then write fixed frames */
	int space = sizeof(p->obuf) - p->obuflen;
	/* Make sure we have enough buffer space to store the frame */
	if (space < len)
		len = space;
	if (swap)
		ast_swapcopy_samples(p->obuf+p->obuflen, buf, len/2);
	else
		memcpy(p->obuf + p->obuflen, buf, len);
	p->obuflen += len;
	while(p->obuflen > frlen) {
		res = write(p->fd, p->obuf, frlen);
		if (res != frlen) {
			if (res < 1) {
/*
 * Card is in non-blocking mode now and it works well now, but there are
 * lot of messages like this. So, this message is temporarily disabled.
 */
				return 0;
			} else {
				ast_log(LOG_WARNING, "Only wrote %d of %d bytes\n", res, frlen);
			}
		}
		p->obuflen -= frlen;
		/* Move memory if necessary */
		if (p->obuflen) 
			memmove(p->obuf, p->obuf + frlen, p->obuflen);
	}
	return len;
}

static int phone_send_text(struct ast_channel *ast, const char *text)
{
    int length = strlen(text);
    return phone_write_buf(ast->tech_pvt, text, length, length, 0) == 
           length ? 0 : -1;
}

static int phone_write(struct ast_channel *ast, struct ast_frame *frame)
{
	struct tapi_pvt *p = ast->tech_pvt;
	int res;
	int maxfr=0;
	char *pos;
	int sofar;
	int expected;
	int codecset = 0;
	char tmpbuf[4];
	/* Write a frame of (presumably voice) data */
	if (frame->frametype != AST_FRAME_VOICE && p->mode != MODE_FXS) {
		if (frame->frametype != AST_FRAME_IMAGE)
			ast_log(LOG_WARNING, "Don't know what to do with  frame type '%d'\n", frame->frametype);
		return 0;
	}
	if (!(frame->subclass.codec &
		(AST_FORMAT_G723_1 | AST_FORMAT_SLINEAR | AST_FORMAT_ULAW | AST_FORMAT_G729A)) && 
	    p->mode != MODE_FXS) {
		ast_log(LOG_WARNING, "Cannot handle frames in %s format\n", ast_getformatname(frame->subclass.codec));
		return -1;
	}
#if 0
	/* If we're not in up mode, go into up mode now */
	if (ast->_state != AST_STATE_UP) {
		ast_setstate(ast, AST_STATE_UP);
		phone_setup(ast);
	}
#else
	if (ast->_state != AST_STATE_UP) {
		/* Don't try tos end audio on-hook */
		return 0;
	}
#endif	
	if (frame->subclass.codec == AST_FORMAT_G729A) {
		if (p->lastformat != AST_FORMAT_G729A) {
			ioctl(p->fd, PHONE_PLAY_STOP);
			ioctl(p->fd, PHONE_REC_STOP);
			if (ioctl(p->fd, PHONE_PLAY_CODEC, G729)) {
				ast_log(LOG_WARNING, "Unable to set G729 mode\n");
				return -1;
			}
			if (ioctl(p->fd, PHONE_REC_CODEC, G729)) {
				ast_log(LOG_WARNING, "Unable to set G729 mode\n");
				return -1;
			}
			p->lastformat = AST_FORMAT_G729A;
			p->lastinput = AST_FORMAT_G729A;
			/* Reset output buffer */
			p->obuflen = 0;
			codecset = 1;
		}
		if (frame->datalen > 80) {
			ast_log(LOG_WARNING, "Frame size too large for G.729 (%d bytes)\n", frame->datalen);
			return -1;
		}
		maxfr = 80;
        } else if (frame->subclass.codec == AST_FORMAT_G723_1) {
		if (p->lastformat != AST_FORMAT_G723_1) {
			ioctl(p->fd, PHONE_PLAY_STOP);
			ioctl(p->fd, PHONE_REC_STOP);
			if (ioctl(p->fd, PHONE_PLAY_CODEC, G723_63)) {
				ast_log(LOG_WARNING, "Unable to set G723.1 mode\n");
				return -1;
			}
			if (ioctl(p->fd, PHONE_REC_CODEC, G723_63)) {
				ast_log(LOG_WARNING, "Unable to set G723.1 mode\n");
				return -1;
			}
			p->lastformat = AST_FORMAT_G723_1;
			p->lastinput = AST_FORMAT_G723_1;
			/* Reset output buffer */
			p->obuflen = 0;
			codecset = 1;
		}
		if (frame->datalen > 24) {
			ast_log(LOG_WARNING, "Frame size too large for G.723.1 (%d bytes)\n", frame->datalen);
			return -1;
		}
		maxfr = 24;
	} else if (frame->subclass.codec == AST_FORMAT_SLINEAR) {
		if (p->lastformat != AST_FORMAT_SLINEAR) {
			ioctl(p->fd, PHONE_PLAY_STOP);
			ioctl(p->fd, PHONE_REC_STOP);
			if (ioctl(p->fd, PHONE_PLAY_CODEC, LINEAR16)) {
				ast_log(LOG_WARNING, "Unable to set 16-bit linear mode\n");
				return -1;
			}
			if (ioctl(p->fd, PHONE_REC_CODEC, LINEAR16)) {
				ast_log(LOG_WARNING, "Unable to set 16-bit linear mode\n");
				return -1;
			}
			p->lastformat = AST_FORMAT_SLINEAR;
			p->lastinput = AST_FORMAT_SLINEAR;
			codecset = 1;
			/* Reset output buffer */
			p->obuflen = 0;
		}
		maxfr = 480;
	} else if (frame->subclass.codec == AST_FORMAT_ULAW) {
		if (p->lastformat != AST_FORMAT_ULAW) {
			ioctl(p->fd, PHONE_PLAY_STOP);
			ioctl(p->fd, PHONE_REC_STOP);
			if (ioctl(p->fd, PHONE_PLAY_CODEC, ULAW)) {
				ast_log(LOG_WARNING, "Unable to set uLaw mode\n");
				return -1;
			}
			if (ioctl(p->fd, PHONE_REC_CODEC, ULAW)) {
				ast_log(LOG_WARNING, "Unable to set uLaw mode\n");
				return -1;
			}
			p->lastformat = AST_FORMAT_ULAW;
			p->lastinput = AST_FORMAT_ULAW;
			codecset = 1;
			/* Reset output buffer */
			p->obuflen = 0;
		}
		maxfr = 240;
	} else {
		if (p->lastformat != frame->subclass.codec) {
			ioctl(p->fd, PHONE_PLAY_STOP);
			ioctl(p->fd, PHONE_REC_STOP);
			if (ioctl(p->fd, PHONE_PLAY_CODEC, (int) frame->subclass.codec)) {
				ast_log(LOG_WARNING, "Unable to set %s mode\n",
					ast_getformatname(frame->subclass.codec));
				return -1;
			}
			if (ioctl(p->fd, PHONE_REC_CODEC, (int) frame->subclass.codec)) {
				ast_log(LOG_WARNING, "Unable to set %s mode\n",
					ast_getformatname(frame->subclass.codec));
				return -1;
			}
			p->lastformat = frame->subclass.codec;
			p->lastinput = frame->subclass.codec;
			codecset = 1;
			/* Reset output buffer */
			p->obuflen = 0;
		}
		maxfr = 480;
	}
 	if (codecset) {
		ioctl(p->fd, PHONE_REC_DEPTH, 3);
		ioctl(p->fd, PHONE_PLAY_DEPTH, 3);
		if (ioctl(p->fd, PHONE_PLAY_START)) {
			ast_log(LOG_WARNING, "Failed to start playback\n");
			return -1;
		}
		if (ioctl(p->fd, PHONE_REC_START)) {
			ast_log(LOG_WARNING, "Failed to start recording\n");
			return -1;
		}
	}
	/* If we get here, we have a frame of Appropriate data */
	sofar = 0;
	pos = frame->data.ptr;
	while(sofar < frame->datalen) {
		/* Write in no more than maxfr sized frames */
		expected = frame->datalen - sofar;
		if (maxfr < expected)
			expected = maxfr;
		/* XXX Internet Phone Jack does not handle the 4-byte VAD frame properly! XXX 
		   we have to pad it to 24 bytes still.  */
		if (frame->datalen == 4) {
			if (p->silencesupression) {
				memcpy(tmpbuf, frame->data.ptr, 4);
				expected = 24;
				res = phone_write_buf(p, tmpbuf, expected, maxfr, 0);
			}
			res = 4;
			expected=4;
		} else {
			int swap = 0;
#if __BYTE_ORDER == __BIG_ENDIAN
			if (frame->subclass.codec == AST_FORMAT_SLINEAR)
				swap = 1; /* Swap big-endian samples to little-endian as we copy */
#endif
			res = phone_write_buf(p, pos, expected, maxfr, swap);
		}
		if (res != expected) {
			if ((errno != EAGAIN) && (errno != EINTR)) {
				if (res < 0) 
					ast_log(LOG_WARNING, "Write returned error (%s)\n", strerror(errno));
	/*
	 * Card is in non-blocking mode now and it works well now, but there are
	 * lot of messages like this. So, this message is temporarily disabled.
	 */
#if 0
				else
					ast_log(LOG_WARNING, "Only wrote %d of %d bytes\n", res, frame->datalen);
#endif
				return -1;
			} else /* Pretend it worked */
				res = expected;
		}
		sofar += res;
		pos += res;
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
				ast_log(LOG_ERROR, "ON CHANNEL %d DETECTED DIGIT: %s\n", i, event.data.dtmf.ascii);
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

static void
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
