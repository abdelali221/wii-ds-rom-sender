/*
 * Copyright (C) 2017 FIX94
 *
 * This software may be modified and distributed under the terms
 * of the MIT license.  See the LICENSE file for details.
 */
#include <gccore.h>
#include <stdio.h>
#include <wiiuse/wpad.h>
#include <ogc/lwp_watchdog.h>
#include <inttypes.h>
#include <malloc.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <dirent.h>
#include <fat.h>
#include "wd.h"
#include "ndsfile.h"

#include "gameyob_bin.h"
#include "nesds_bin.h"
#include "demomenu_bin.h"

enum {
	/* Download Play */
	WD_STATE_DSWAIT = 0,
	WD_STATE_GETNAME,
	WD_STATE_SENDRSA,
	WD_STATE_IDLERSA,
	WD_STATE_SENDDATA,
	WD_STATE_POSTSEND,
	/* DS Download Station Emu */
	WD_STATE_STATIONMENUWAIT,
	WD_STATE_STATIONMENULENIDLE,
	WD_STATE_STATIONMENULEN,
	WD_STATE_STATIONMENUWAITLEN,
	WD_STATE_STATIONMENUDATAIDLE,
	WD_STATE_STATIONMENUDATA,
	WD_STATE_STATIONMENUIDLE,
	WD_STATE_STATIONWAITSELECT,
	WD_STATE_STATIONDATALENIDLE,
	WD_STATE_STATIONDATALEN,
	WD_STATE_STATIONDATAWAITLEN,
	WD_STATE_STATIONDATAIDLE,
	WD_STATE_STATIONSENDDATA,
	WD_STATE_STATIONPOST,
};

static volatile bool mpdl_active = false;
static volatile bool wd_has_rsa = true;
static volatile bool wd_hdr_valid = true;
static volatile bool wd_haxxstation = false;
static volatile bool gotResponse = false;
static volatile bool sendError = false;
static volatile uint8_t wd_namestate = 0;
static volatile uint32_t wd_idle = 0;
static volatile uint16_t wd_last_datapos = 0;
static volatile uint16_t wd_datapos = 0;
static volatile uint32_t wd_databufpos = 0;
static volatile int wd_state = WD_STATE_DSWAIT;
static volatile char wd_c1_name[11];
static volatile int16_t connected = 0;
static volatile bool beaconActive = true;

//Using a total of 4 Threads
#define STACKSIZE 0x8000

static uint8_t mpdl_stack[STACKSIZE];
static uint8_t mpdl_inf_stack[STACKSIZE];
static uint8_t mpdl_send_stack[STACKSIZE];
static uint8_t mpdl_recv_stack[STACKSIZE];

static lwp_t mpdl_thread_ptr;
static lwp_t mpdl_inf_thread_ptr;
static lwp_t mpdl_recv_thread_ptr;
static lwp_t mpdl_send_thread_ptr;

static uint8_t wdGameInfo[0x500] __attribute__((aligned(32)));
static uint8_t *demomenubuf = NULL, *demodatabuf = NULL;
static uint32_t demomenulen, demodatalen, demomenupkg, demodatapkg;
static s32 __wd_fd;

static void* mpdl_thread(void * nul)
{

	int cInf = 0;

	while(mpdl_active)
	{
		if(beaconActive)
		{
			uint16_t beaconIn = (uint16_t)(ticks_to_microsecs(gettick())/64);

			uint8_t *dat = wdGameInfo+(cInf<<7);

			if(wd_state == WD_STATE_SENDDATA)
				dat[0xB] = 2;
			else
				dat[0xB] = 3;

			if(connected & (1<<1))
				dat[0x16] = 1;
			else
				dat[0x16] = 0;

			s32 ret = WD_ChangeBeacon(beaconIn, dat, 0x80);
			if(ret != 0) printf("WD_SendBeacon Err 0x%x\n", ret);

			cInf++;
			if(cInf >= 10)
				cInf = 0;
		}
		usleep(200*1000);
	}
	return nul;
}

static uint8_t wdReq[0x94] __attribute__((aligned(32)));
static uint8_t chan1Con[6] __attribute__((aligned(32)));
static void* mpdl_inf_thread(void * nul)
{
	while(mpdl_active)
	{
		s32 ret = WD_RecvNotification(wdReq, 0x94);
		if(ret != 0)
			printf("\rWD_RecvNotification Err 0x%x", ret);
		else
		{
			int32_t ret = 0;
			memcpy(&ret, wdReq, 4);
			int16_t chan = 0;
			memcpy(&chan, wdReq+0xE, 2);
			if(ret == 0 && chan)
			{
				//printf("DS On Channel %d connected\n", chan);
				if(chan == 1)
				{
					connected |= (1<<chan);
					wd_namestate = 0;
					memset((void*)wd_c1_name, 0, 11);
					wd_state = WD_STATE_GETNAME;
					memcpy(chan1Con, wdReq+8, 6);
					beaconActive = false;
				}
				else
				{
					//printf("Channel %d not supported, forcing disconnect\n", chan);
					ret = WD_DisAssoc(wdReq+8, 6);
					if(ret != 0) printf("WD_DisAssoc Err 0x%x\n", ret);
				}
			}
			else if(ret == 1 && chan)
			{
				//printf("DS On Channel %d disconnected\n", chan);
				if(chan == 1)
				{
					connected &= ~(1<<chan);
					wd_state = WD_STATE_DSWAIT;
					beaconActive = true;
				}
			}
			else if(ret == 5 && chan)
				sendError = true;
			else if(ret != 3)
				printf("DS Ret %d Chan %d\n", ret, chan);
		}
	}
	return nul;
}

static uint8_t wdRecvFrame[0x2000] __attribute__((aligned(32)));
static char stationname[10] = { 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20 };

static void* mpdl_recv_thread(void * nul)
{
	memset((void*)wd_c1_name, 0, 11);
	while(mpdl_active)
	{
		s32 ret = WD_ReceiveFrame(wdRecvFrame, 0x2000);
		if(ret > 0xA && wdRecvFrame[0xB] > 0 && wdRecvFrame[0x12] == 4)
		{
			uint8_t port = (wdRecvFrame[0x13]&0xF);
			uint8_t reply = wdRecvFrame[0x14];
			uint8_t seq = wdRecvFrame[0x15];
			if(port == 1)
			{
				if(wd_state == WD_STATE_GETNAME && reply == 7 && seq < 5)
				{
					wd_namestate |= 1<<seq;
					if(seq)
					{
						uint8_t off = (seq-1)*3;
						wd_c1_name[off] = wdRecvFrame[0x16];
						if(seq < 4)
						{
							wd_c1_name[off+1] = wdRecvFrame[0x18];
							wd_c1_name[off+2] = wdRecvFrame[0x1A];
						}
					}
					if(wd_namestate == 0x1F)
					{
						wd_state = WD_STATE_SENDRSA;
						wd_datapos = 0;
						wd_last_datapos = 0;
						wd_databufpos = 0;
					}
				}
				else if(wd_state == WD_STATE_SENDRSA && reply == 8)
				{
					//printf("Sent RSA Signature to \"%.10s\"\n", wd_c1_name);
					if(memcmp((void*)wd_c1_name, stationname, 10) == 0)
					{
						wd_state = WD_STATE_STATIONMENUWAIT;
						wd_idle = 0;
						//printf("Download Station Init\n");
					}
					else
					{
						wd_state = WD_STATE_IDLERSA;
						wd_idle = 0;
						//printf("Waiting for a bit\n");
					}
				}
				else if(wd_state == WD_STATE_IDLERSA)
				{
					wd_idle++;
					if(wd_idle >= 60)
					{
						wd_state = WD_STATE_SENDDATA;
						//printf("Done Waiting, sending Data\n");
					}
				}
				else if(wd_state == WD_STATE_SENDDATA)
				{
					if(reply == 9)
					{
						uint16_t tmp;
						//memcpy(&tmp, wdRecvFrame+0x15, 2); //stat, blocks received in a row
						memcpy(&tmp, wdRecvFrame+0x17, 2); //next requested block
						wd_datapos = __builtin_bswap16(tmp);
						if(wd_datapos > 0) //0 is hdr, 1-end is rom
						{
							//printf("Requested ROM segment %d\n", wd_datapos-1);
							wd_databufpos=(0x1EA*(wd_datapos-1)); //ROM segment is always 0x1EA bytes
						}
					}
					else if(reply == 10)
					{
						//printf("Done sending Data, sent %d segments\n", wd_datapos);
						wd_state = WD_STATE_POSTSEND;
					}
				}
				else if(wd_state == WD_STATE_POSTSEND && reply == 11)
				{
					//printf("DS is starting\n");
					//force disconnect channel 1
					connected &= ~(1<<1);
					wd_state = WD_STATE_DSWAIT;
				}
				else if(wd_state == WD_STATE_STATIONMENULENIDLE)
				{
					wd_idle++;
					if(wd_idle >= 10)
						wd_state = WD_STATE_STATIONMENULEN;
				}
				else if(wd_state == WD_STATE_STATIONDATALENIDLE)
				{
					wd_idle++;
					if(wd_idle >= 10)
						wd_state = WD_STATE_STATIONDATALEN;
				}
				else if(wd_state == WD_STATE_STATIONMENUDATAIDLE)
				{
					wd_idle++;
					if(wd_idle >= 60)
						wd_state = WD_STATE_STATIONMENUDATA;
				}
				else if(wd_state == WD_STATE_STATIONMENUIDLE)
				{
					wd_idle++;
					if(wd_idle >= 5)
						wd_state = WD_STATE_STATIONMENUDATA;
				}
				else if(wd_state == WD_STATE_STATIONDATAIDLE)
				{
					wd_idle++;
					if(wd_idle >= 5)
						wd_state = WD_STATE_STATIONSENDDATA;
				}
				else
					gotResponse = true;
			}
			else 
			{
				if(port == 0xD && wd_state == WD_STATE_STATIONMENUWAIT && memcmp(wdRecvFrame+0x14, "demomenu", 8) == 0)
				{
					wd_idle = 0;
					wd_state = WD_STATE_STATIONMENULENIDLE;
				}
				else if(port == 0xE && (wd_state == WD_STATE_STATIONMENULEN || wd_state == WD_STATE_STATIONMENUWAITLEN))
				{
					wd_idle = 0;
					wd_state = WD_STATE_STATIONMENUDATAIDLE;
				}
				else if(port == 0xD && wd_state == WD_STATE_STATIONWAITSELECT && memcmp(wdRecvFrame+0x14, "file.nds", 8) == 0)
				{
					wd_idle = 0;
					wd_state = WD_STATE_STATIONDATALENIDLE;
					wd_datapos = 0xFFFE;
				}
				else if(port == 0xF && (wd_state == WD_STATE_STATIONDATALEN || wd_state == WD_STATE_STATIONDATAWAITLEN))
				{
					wd_idle = 0;
					wd_state = WD_STATE_STATIONDATAIDLE;
				}
			}
		}
	}
	return nul;
}

static const uint8_t idle_msg[3] = {
	0x01, 0x01, 0x00,
};

static const uint8_t id_req_msg[5] = {
	0x11, 0x01, 0x01, 0x00, 0x02
};

static const uint8_t rsa_msg_start[3] = {
	0x11, 0x73, 0x03
};

static const uint8_t hdr_msg_start[5] = {
	0x11, 0xB3, 0x04, 0x00, 0x00
};

static const uint8_t data_msg_start[5] = {
	0x11, 0xF8, 0x04, 0x00, 0x00
};

static const uint8_t postsend_msg[5] = {
	0x11, 0x01, 0x05, 0x00, 0x02
};

static const uint8_t stationlen_msg[10] = {
	0x0D, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x02, 0x02
};

static const uint8_t msg_end[2] = {
	0x02, 0x00 
};

static void wdDoSend(uint8_t *send_buf, u32 in_len)
{

	uint16_t cTime = (uint16_t)(ticks_to_microsecs(gettick())/64);
	s32 ret = WD_ChangeVTSF(cTime);
	if(ret < 0)	printf("WD_ChangeVTSF=0x%x\n", ret);
	ret = WD_MpSendFrame(send_buf, in_len, send_buf+0x200, 0x10);
	if(ret) printf("SendFrame Err 0x%x\n", ret);
}

static uint8_t srlHdr[0x160];
static uint8_t srlRSA[0x88];
static uint8_t *arm_databuf;
static uint32_t arm_datalen_total;
static uint16_t arm_datapkg_total;

static const uint16_t sleepArr[8][3] = 
{
	{ 6000, 2500, 2400 },
	{ 7500, 3125, 3000 },
	{ 9000, 3750, 3600 },
	{10500, 4375, 4200 },
	{12000, 5000, 4800 },
	{ 4000, 1975, 1800 },
	{ 3000, 1250, 1200 },
	{ 1500, 625,  600  }
};
static const char sleepDispArr[8][6] = 
{
	"1x", "1.25x", "1.5x", "1.75x", "2x", "0.75x", "0.5x", "0.25x"
};

static uint8_t sleepVal = 0;

int sendVal = 0;
static bool sendTimes(uint8_t *send_buf, u32 in_len, uint8_t times)
{
	if(sendVal < times)
	{
		if(sendVal && gotResponse && !sendError)
		{
			gotResponse = false;
			sendVal++;
		}
		if(sendVal < times)
		{
			//clear send error
			sendError = false;
			wdDoSend(send_buf, in_len);
			//only accept new response AFTER sending this block
			gotResponse = false;
			if(!sendVal) sendVal = 1;
		}
		return false;
	}
	else
		return true;
}

//new package only gets sent when this number here
//changed from the previous package number, else
//WD just thinks its the same package again
static uint8_t packnum = 0;
static void* mpdl_send_thread(void * nul)
{
	uint8_t *wdSendBuf = calloc(1, 0x210);
	//some raw WD config
	memset(wdSendBuf+0x200,0,0x10);
	wdSendBuf[0x207] = 0xC; //A and C works, C used by official games
	wdSendBuf[0x209] = (1<<1); //only chan 1 atm
	uint16_t tmp16, portLen;
	uint32_t tmp32;
	while(mpdl_active)
	{
		//Only handle Channel 1 for now
		if((connected & (1<<1)))
		{
			switch(wd_state)
			{
				case WD_STATE_GETNAME:
					memcpy(wdSendBuf, id_req_msg, sizeof(id_req_msg));
					wdDoSend(wdSendBuf, 6);
					usleep(sleepArr[sleepVal][0]);
					break;
				case WD_STATE_SENDRSA:
					memcpy(wdSendBuf, rsa_msg_start, sizeof(rsa_msg_start));
					memcpy(wdSendBuf+0x3, srlHdr+0x24, 4); //ARM9 Entry
					memcpy(wdSendBuf+0x7, srlHdr+0x34, 4); //ARM7 Entry
					tmp32 = __builtin_bswap32(0x027FFE00);
					memcpy(wdSendBuf+0xF, &tmp32, 4); //Header Dest 1
					memcpy(wdSendBuf+0x13, &tmp32, 4); //Header Dest 2
					tmp32 = __builtin_bswap32(0x160);
					memcpy(wdSendBuf+0x17, &tmp32, 4); //Header Len
					memcpy(wdSendBuf+0x1F, srlHdr+0x28, 4); //ARM9 Dest (tmp)
					memcpy(wdSendBuf+0x23, srlHdr+0x28, 4); //ARM9 Dest (actual)
					memcpy(wdSendBuf+0x27, srlHdr+0x2C, 4); //ARM9 Size
					tmp32 = __builtin_bswap32(0x022C0000);
					memcpy(wdSendBuf+0x2F, &tmp32, 4); //ARM7 Dest (tmp)
					memcpy(wdSendBuf+0x33, srlHdr+0x38, 4); //ARM7 Dest (actual)
					memcpy(wdSendBuf+0x37, srlHdr+0x3C, 4); //ARM7 Size
					tmp32 = __builtin_bswap32(1);
					memcpy(wdSendBuf+0x3B, &tmp32, 4); //RSA Header End
					if(wd_has_rsa) //RSA Data
						memcpy(wdSendBuf+0x3F, srlRSA, 0x88);
					memcpy(wdSendBuf+0xE7, &packnum, 1); packnum++;
					memcpy(wdSendBuf+0xE8, msg_end, sizeof(msg_end));
					//printf("Sending RSA Signature\n");
					wdDoSend(wdSendBuf, 0xEA);
					usleep(sleepArr[sleepVal][0]);
					break;
				case WD_STATE_SENDDATA:
					wd_last_datapos = wd_datapos;
					uint32_t sendLen;
					if(wd_datapos == 0)
					{
						memcpy(wdSendBuf, hdr_msg_start, sizeof(hdr_msg_start));
						tmp16 = __builtin_bswap16(wd_datapos);
						memcpy(wdSendBuf+5, &tmp16, 2);
						memcpy(wdSendBuf+7, srlHdr, 0x160);
						memcpy(wdSendBuf+0x167, &packnum, 1); packnum++;
						memcpy(wdSendBuf+0x168, msg_end, sizeof(msg_end));
						sendLen = 0x16A;
					}
					else
					{
						memcpy(wdSendBuf, data_msg_start, sizeof(data_msg_start));
						tmp16 = __builtin_bswap16(wd_datapos);
						memcpy(wdSendBuf+5, &tmp16, 2);
						memcpy(wdSendBuf+7, arm_databuf+wd_databufpos, 0x1EA);
						memcpy(wdSendBuf+0x1F1, &packnum, 1); packnum++;
						memcpy(wdSendBuf+0x1F2, msg_end, sizeof(msg_end));
						sendLen = 0x1F4;
					}
					wdDoSend(wdSendBuf, sendLen);
					usleep(sleepArr[sleepVal][0]);
					break;
				case WD_STATE_POSTSEND:
					memcpy(wdSendBuf, postsend_msg, sizeof(postsend_msg));
					wdDoSend(wdSendBuf, 6);
					usleep(sleepArr[sleepVal][0]);
					break;
				case WD_STATE_STATIONMENULEN:
					memcpy(wdSendBuf, stationlen_msg, sizeof(stationlen_msg));
					tmp32 = __builtin_bswap32(demomenulen);
					memcpy(wdSendBuf+2, &tmp32, 4);
					memset(wdSendBuf+6, 0, 2);
					memcpy(wdSendBuf+8, msg_end, sizeof(msg_end));
					if(sendTimes(wdSendBuf, 10, 32))
					{
						sendVal = 0;
						wd_state = WD_STATE_STATIONMENUWAITLEN;
					}
					usleep(sleepArr[sleepVal][0]);
					break;
				case WD_STATE_STATIONMENUDATA:
					wd_idle = 0;
					tmp16 = __builtin_bswap16(wd_datapos);
					portLen = 0x1E00;
					if(demomenulen == wd_databufpos)
					{
						portLen |= 1;
						memcpy(wdSendBuf, &portLen, 2);
						memcpy(wdSendBuf+2, &tmp16, 2);
						memcpy(wdSendBuf+4, (void*)&wd_datapos, 2);
						memcpy(wdSendBuf+6, msg_end, sizeof(msg_end));
						if(sendTimes(wdSendBuf, 8, 32))
						{
							sendVal = 0;
							wd_state = WD_STATE_STATIONWAITSELECT;
						}
					}
					else if((demomenulen-wd_databufpos) <= 0x1E)
					{
						portLen |= ((demomenulen-wd_databufpos)>>1)+1;
						memcpy(wdSendBuf, &portLen, 2);
						memcpy(wdSendBuf+2, &tmp16, 2);
						memcpy(wdSendBuf+4, demomenubuf+wd_databufpos, (demomenulen-wd_databufpos));
						memcpy(wdSendBuf+4+(demomenulen-wd_databufpos), (void*)&wd_datapos, 2);
						memcpy(wdSendBuf+6+(demomenulen-wd_databufpos), msg_end, sizeof(msg_end));
						if(sendTimes(wdSendBuf, 8+(demomenulen-wd_databufpos), 32))
						{
							sendVal = 0;
							wd_datapos = 0xFFFF;
							wd_databufpos = demomenulen;
							wd_state = WD_STATE_STATIONMENUIDLE;
						}
					}
					else
					{
						portLen |= 0x10;
						memcpy(wdSendBuf, &portLen, 2);
						memcpy(wdSendBuf+2, &tmp16, 2);
						memcpy(wdSendBuf+4, demomenubuf+wd_databufpos, 0x1E);
						memcpy(wdSendBuf+0x22, (void*)&wd_datapos, 2);
						memcpy(wdSendBuf+0x24, msg_end, sizeof(msg_end));
						if(sendTimes(wdSendBuf, 0x26, wd_datapos ? 2 : 32))
						{
							sendVal = 0;
							wd_datapos++;
							wd_databufpos+=0x1E;
							if(demomenulen == wd_databufpos)
							{
								wd_state = WD_STATE_STATIONMENUIDLE;
								wd_datapos = 0xFFFF;
							}
						}
					}
					usleep(sleepArr[sleepVal][1]);
					break;
				case WD_STATE_STATIONDATALEN:
					memcpy(wdSendBuf, stationlen_msg, sizeof(stationlen_msg));
					tmp32 = __builtin_bswap32(demodatalen);
					memcpy(wdSendBuf+2, &tmp32, 4);
					memset(wdSendBuf+6, 1, 2);
					memcpy(wdSendBuf+8, msg_end, sizeof(msg_end));
					if(sendTimes(wdSendBuf, 10, 32))
					{
						sendVal = 0;
						wd_state = WD_STATE_STATIONDATAWAITLEN;
					}
					usleep(sleepArr[sleepVal][0]);
					break;
				case WD_STATE_STATIONSENDDATA:
					wd_idle = 0;
					tmp16 = __builtin_bswap16(wd_datapos);
					portLen = 0x1F00;
					if(wd_datapos == 0xFFFE)
					{
						portLen |= 0x10;
						memcpy(wdSendBuf, &portLen, 2);
						memcpy(wdSendBuf+2, &tmp16, 2);
						memset(wdSendBuf+4, 0, 0x1E);
						memcpy(wdSendBuf+0x22, (void*)&wd_datapos, 2);
						memcpy(wdSendBuf+0x24, msg_end, sizeof(msg_end));
						if(sendTimes(wdSendBuf, 0x26, 32))
						{
							sendVal = 0;
							wd_datapos = 0;
							wd_databufpos = 0;
						}
					}
					else if(demodatalen == wd_databufpos)
					{
						portLen |= 1;
						memcpy(wdSendBuf, &portLen, 2);
						memcpy(wdSendBuf+2, &tmp16, 2);
						memcpy(wdSendBuf+4, (void*)&wd_datapos, 2);
						memcpy(wdSendBuf+6, msg_end, sizeof(msg_end));
						if(sendTimes(wdSendBuf, 8, 32))
						{
							sendVal = 0;
							wd_state = WD_STATE_STATIONPOST;
						}
					}
					else if((demodatalen-wd_databufpos) <= 0x7E)
					{
						portLen |= ((demodatalen-wd_databufpos)>>1)+1;
						memcpy(wdSendBuf, &portLen, 2);
						memcpy(wdSendBuf+2, &tmp16, 2);
						memcpy(wdSendBuf+4, demodatabuf+wd_databufpos, (demodatalen-wd_databufpos));
						memcpy(wdSendBuf+4+(demodatalen-wd_databufpos),(void*) &wd_datapos, 2);
						memcpy(wdSendBuf+6+(demodatalen-wd_databufpos), msg_end, sizeof(msg_end));
						if(sendTimes(wdSendBuf, 8+(demodatalen-wd_databufpos), 32))
						{
							sendVal = 0;
							wd_datapos = 0xFFFF;
							wd_databufpos = demodatalen;
							wd_state = WD_STATE_STATIONDATAIDLE;
						}
					}
					else
					{
						portLen |= 0x40;
						memcpy(wdSendBuf, &portLen, 2);
						memcpy(wdSendBuf+2, &tmp16, 2);
						memcpy(wdSendBuf+4, demodatabuf+wd_databufpos, 0x7E);
						memcpy(wdSendBuf+0x82, (void*)&wd_datapos, 2);
						memcpy(wdSendBuf+0x84, msg_end, sizeof(msg_end));
						if(sendTimes(wdSendBuf, 0x86, wd_datapos ? 2 : 32))
						{
							sendVal = 0;
							wd_datapos++;
							wd_databufpos+=0x7E;
							if(demodatalen == wd_databufpos)
							{
								wd_state = WD_STATE_STATIONDATAIDLE;
								wd_datapos = 0xFFFF;
							}
							continue;
						}
					}
					usleep(sleepArr[sleepVal][2]);
					break;
				default:
					memcpy(wdSendBuf, idle_msg, sizeof(idle_msg));
					wdDoSend(wdSendBuf, 4);
					usleep(sleepArr[sleepVal][0]);
					break;
			}
		}
		else
			usleep(500);
	}
	//some raw WD config
	wdSendBuf[0x209] = 0; //send to ourself

	//Force wake up Receive Thread by sending something
	memcpy(wdSendBuf, idle_msg, sizeof(idle_msg));
	wdDoSend(wdSendBuf, 4);

	free(wdSendBuf);

	return nul;
}

#define IOCTL_ExecSuspendScheduler	1

static bool inited = false;

static void printmain()
{
	printf("\x1b[2J");
	printf("\x1b[37m");
	printf("Wii DS ROM Sender v3.4 by FIX94 & Abdelali221\n");
	printf("HaxxStation by shutterbug2000, Gericom, and Apache Thunder\n\n");
}

static void printstatus()
{
	if(!wd_hdr_valid)
		printf("WARNING:\nROM Header appears to be invalid, it may not work\n");
	if(!wd_has_rsa && !wd_haxxstation)
		printf("WARNING:\nNo HaxxStation and ROM unsigned, it will only work on a DS with FlashMe\n");
	printf("Current Status:\n");
	if(!inited)
		printf("Initializing System, this may take a while\n");
	else
	{
		switch(wd_state)
		{
			case WD_STATE_DSWAIT:
				printf("Waiting for DS to connect, Press any Button to go back into ROM Selection\n");
				break;
			case WD_STATE_GETNAME:
				printf("DS Connected!\n");
				break;
			case WD_STATE_SENDRSA:
				printf("Sending RSA\n");
				break;
			case WD_STATE_IDLERSA:
				printf("Sent RSA, waiting\n");
				break;
			case WD_STATE_SENDDATA:
				printf("Sending Data to DS \"%.10s\" (%d/%d Packets)\n", wd_c1_name, wd_datapos, arm_datapkg_total);
				break;
			case WD_STATE_POSTSEND:
				printf("Done Sending Data to DS!\n");
				break;
			case WD_STATE_STATIONMENUWAIT:
				printf("[Download Station] Connected!\n");
				break;
			case WD_STATE_STATIONMENULENIDLE:
				printf("[Download Station] Waiting\n");
				break;
			case WD_STATE_STATIONMENULEN:
				printf("[Download Station] Sending Menu Length\n");
				break;
			case WD_STATE_STATIONMENUWAITLEN:
				printf("[Download Station] Waiting for Menu Length Response\n");
				break;
			case WD_STATE_STATIONMENUDATAIDLE:
				printf("[Download Station] Preparing to send Menu\n");
				break;
			case WD_STATE_STATIONMENUDATA:
				printf("[Download Station] Sending Menu (%d/%d Packets)\n", wd_datapos, demomenupkg);
				break;
			case WD_STATE_STATIONMENUIDLE:
				printf("[Download Station] Menu Sent!\n");
				break;
			case WD_STATE_STATIONWAITSELECT:
				printf("[Download Station] Waiting for Game Selection\n");
				break;
			case WD_STATE_STATIONDATALENIDLE:
				printf("[Download Station] Waiting\n");
				break;
			case WD_STATE_STATIONDATALEN:
				printf("[Download Station] Sending Game Length\n");
				break;
			case WD_STATE_STATIONDATAWAITLEN:
				printf("[Download Station] Waiting for Game Length Response\n");
				break;
			case WD_STATE_STATIONDATAIDLE:
				printf("[Download Station] Preparing to send Game\n");
				break;
			case WD_STATE_STATIONSENDDATA:
				printf("[Download Station] Sending Game (%d/%d Packets)\n", wd_datapos, demodatapkg);
				break;
			case WD_STATE_STATIONPOST:
				printf("[Download Station] Game Sent!\n");
				break;
		}
	}
}

typedef struct _srlNames {
	char name[256];
} srlNames;

static int compare (const void * a, const void * b ) {
	return strcmp((*(srlNames*)a).name, (*(srlNames*)b).name);
}

static bool dsVerifyHdr()
{
	uint16_t crc = ndsfile_crc(srlHdr, 0x15E);
	uint16_t inCrc = srlHdr[0x15E]|(srlHdr[0x15F]<<8);
	return (crc == inCrc);
}

uint16_t UTF8toUTF16(char chr) 
{
	return chr << 8;
}

void u8strtou16(char* src, uint16_t* dest, int n)
{
	for(int i = 0; i < n; i++) {
		dest[i] = src[i] << 8;
	}
}

int main() 
{
	void *xfb = NULL;
	GXRModeObj *rmode = NULL;
	VIDEO_Init();
	rmode = VIDEO_GetPreferredMode(NULL);
	xfb = MEM_K0_TO_K1(SYS_AllocateFramebuffer(rmode));
	VIDEO_Configure(rmode);
	VIDEO_SetNextFramebuffer(xfb);
	VIDEO_SetBlack(FALSE);
	VIDEO_Flush();
	VIDEO_WaitVSync();
	if(rmode->viTVMode&VI_NON_INTERLACE)
		VIDEO_WaitVSync();

	int x = 24, y = 32, w, h;
	w = rmode->fbWidth - (32);
	h = rmode->xfbHeight - (48);
	CON_InitEx(rmode, x, y, w, h);
	VIDEO_ClearFrameBuffer(rmode, xfb, COLOR_BLACK);

	printmain();
	printstatus();

	printf("Reloading into IOS21\n");
	//Known to properly work with DS
	IOS_ReloadIOS(21);

	printf("PAD Init\n");
	PAD_Init();
	WPAD_Init();
	printf("FAT Init\n");
	fatInitDefault();
	printf("Parsing srl directory\n");
	int srlCnt = 0;
	DIR *dir = opendir("/srl");
	struct dirent *dent = NULL;
	srlNames *names = NULL;
	if(dir!=NULL)
	{
		while((dent=readdir(dir))!=NULL)
		{
			if(strstr(dent->d_name,".srl") != NULL
				|| strstr(dent->d_name,".nds") != NULL
				|| strstr(dent->d_name,".gb") != NULL
				|| strstr(dent->d_name,".nes") != NULL)
				srlCnt++;
		}
		closedir(dir);
		if(srlCnt)
		{
			names = malloc(sizeof(srlNames)*srlCnt);
			memset(names,0,sizeof(srlNames)*srlCnt);
			dir = opendir("/srl");
			int i = 0;
			while((dent=readdir(dir))!=NULL)
			{
				if(strstr(dent->d_name,".srl") != NULL
					|| strstr(dent->d_name,".nds") != NULL
					|| strstr(dent->d_name,".gb") != NULL
					|| strstr(dent->d_name,".nes") != NULL)
				{
					strcpy(names[i].name,dent->d_name);
					i++;
				}
			}
			closedir(dir);
		}
	}
	if(srlCnt == 0 || names == NULL)
	{
		printf("No Files! Make sure you have .srl/.nds files in your \"srl\" folder!\n");
		VIDEO_WaitVSync();
		VIDEO_WaitVSync();
		sleep(5);
		return 0;
	}
	qsort(names, srlCnt, sizeof(srlNames), compare);

	printf("Stopping WC24\n");

	//WC24SuspendScheduler
	u32 out = 0;
	s32 kd_fd = IOS_Open("/dev/net/kd/request", 0);
	if(kd_fd < 0)
	{
		printf("KD Open Err %d\n", kd_fd);
		VIDEO_WaitVSync();
		VIDEO_WaitVSync();
		sleep(5);
		free(names);
		return 0;
	}
	IOS_Ioctl(kd_fd, IOCTL_ExecSuspendScheduler, NULL, 0, &out, 4);
	IOS_Close(kd_fd);

	printf("Locking Wireless Driver...");

	s32 lockid = NCD_LockWirelessDriver();
	if(lockid < 0)
	{
		printf("NCDLockWirelessDriver failed: lockid=0x%x\n", lockid);
		VIDEO_WaitVSync();
		VIDEO_WaitVSync();
		sleep(5);
		free(names);
		return 0;
	}
	printf("Done.\n");
	int ret = 0;

	
	//make sure LZO is ready when we need it
	demomenubuf = ndsfile_demomenu_start(&demomenulen);

	//allocate big buffers at once
	//__wd_hid = iosCreateHeap(0x8000);
	arm_databuf = malloc(0x400000);
	uint8_t *srlBuf = malloc(0x400000);
	//for HaxxStation
	uint8_t *clientBuf = malloc(0x400000);

	uint8_t tmpWdIconBuf[0x220];

	while(1)
	{
		bool selected = false;
		int i = 0;
		while(1)
		{
			PAD_ScanPads();
			WPAD_ScanPads();

			u32 btns = PAD_ButtonsDown(0);
			u32 wbtns = WPAD_ButtonsDown(0);
			if((btns & PAD_BUTTON_A) || (wbtns & WPAD_BUTTON_A) || 
				(wbtns & WPAD_CLASSIC_BUTTON_A))
			{
				printf("\nPreparing broadcast...");
				selected = true;
				break;
			}
			else if((btns & PAD_BUTTON_B) || (wbtns & WPAD_BUTTON_B) || 
				(wbtns & WPAD_CLASSIC_BUTTON_B))
			{
				sleepVal++;
				if(sleepVal >= 8)
					sleepVal = 0;
			}
			else if((btns & PAD_BUTTON_RIGHT) || (wbtns & WPAD_BUTTON_RIGHT) || 
				(wbtns & WPAD_CLASSIC_BUTTON_RIGHT))
			{
				i++;
				if(i >= srlCnt) i = 0;
			}
			else if((btns & PAD_BUTTON_LEFT) || (wbtns & WPAD_BUTTON_LEFT) || 
				(wbtns & WPAD_CLASSIC_BUTTON_LEFT))
			{
				i--;
				if(i < 0) i = (srlCnt-1);
			}
			else if((btns & PAD_BUTTON_START) || (wbtns & WPAD_BUTTON_HOME) || 
				(wbtns & WPAD_CLASSIC_BUTTON_HOME))
				break;

			printmain();
			printf("Select ROM file or press HOME/START to exit\n");
			printf("<< %s >>\n",names[i].name);
			printf("Press B to change the delay timing\n");
			printf("Delay Timing: %s\n", sleepDispArr[sleepVal]);

			VIDEO_WaitVSync();
		}
		if(!selected)
			break;

		char romF[262];
		sprintf(romF,"/srl/%s",names[i].name);
		printf("\nOpening ROM...");
		FILE *f = fopen(romF,"rb");
		if(f == NULL) continue;
		printf("Done.\n");
		fseek(f,0,SEEK_END);
		size_t srlSize = ftell(f);
		rewind(f);
		if(strstr(names[i].name,".gb") != 0)
		{
			if(srlSize > 0x200000)
			{
				printf("ROM too big for NDS RAM!\n");
				VIDEO_WaitVSync();
				sleep(2);
				fclose(f);
				continue;
			}
			memcpy(srlBuf,gameyob_bin,gameyob_bin_size);
			fread(srlBuf+0x9B0B0,1,srlSize,f);
			fclose(f);
			//gameyob uses length for bank count
			uint32_t wLen = __builtin_bswap32(srlSize);
			memcpy(srlBuf+0x29B0B0,&wLen,4);
		}
		else if(strstr(names[i].name,".nes") != 0)
		{
			if(srlSize > 0x200000)
			{
				printf("ROM too big for NDS RAM!\n");
				VIDEO_WaitVSync();
				sleep(2);
				fclose(f);
				continue;
			}
			memcpy(srlBuf,nesds_bin,nesds_bin_size);
			fread(srlBuf+0xDA60,1,srlSize,f);
			fclose(f);
			//nesds does not need length
		}
		else
		{
			if(srlSize > 0x400000)
			{
				printf("ROM too big for NDS RAM!\n");
				VIDEO_WaitVSync();
				sleep(2);
				fclose(f);
				continue;
			}
			fread(srlBuf,1,srlSize,f);
			fclose(f);
		}
		if(ndsfile_station_open())
		{
			size_t tmpLen;
			size_t clientSize;
			if(!ndsfile_station_getfile(clientBuf,&clientSize,"ds_demo_client.srl") ||
				!ndsfile_station_getfile(tmpWdIconBuf,&tmpLen,"icon.nbfp") ||
				!ndsfile_station_getfile(tmpWdIconBuf+0x20,&tmpLen,"icon.nbfc"))
			{
				printf("Invalid haxxstation.nds! Sending file directly\n");
				sleep(2);
			}
			else
			{
				wd_haxxstation = true;
				//move srlBuf
				demodatalen = srlSize;
				demodatabuf = ndsfile_haxx_start(srlBuf, &demodatalen);
				demomenupkg = demomenulen/0x1E;
				demodatapkg = demodatalen/0x7E;
				//replace srlBuf with client now
				memcpy(srlBuf, clientBuf, clientSize);
				srlSize = clientSize;
			}
			ndsfile_station_close();
		}

		//srlBuf contains file to send
		memcpy(srlHdr,srlBuf,0x160);

		//Set up file buffer to send
		uint32_t tmp;
		memcpy(&tmp, srlHdr+0x20, 4);
		uint32_t arm9off = __builtin_bswap32(tmp);
		memcpy(&tmp, srlHdr+0x2C, 4);
		uint32_t arm9len = __builtin_bswap32(tmp);
		uint32_t arm9cpLen = arm9len-(arm9len%0x1EA);

		memcpy(&tmp, srlHdr+0x30, 4);
		uint32_t arm7off = __builtin_bswap32(tmp);
		memcpy(&tmp, srlHdr+0x3C, 4);
		uint32_t arm7len = __builtin_bswap32(tmp);
		uint32_t arm7cpLen = arm7len-(arm7len%0x1EA);
		
		arm_datalen_total = arm9cpLen+arm7cpLen;
		if(arm9cpLen < arm9len) //Add extra ARM9 Block to fill
			arm_datalen_total+=0x1EA;
		if(arm7cpLen < arm7len) //Add extra ARM7 Block to fill
			arm_datalen_total+=0x1EA;

		if(arm_datalen_total > 0x400000)
		{
			printf("ARM Binaries too big for NDS RAM!\n");
			VIDEO_WaitVSync();
			sleep(2);
			continue;
		}

		memset(arm_databuf, 0, arm_datalen_total);
		arm_datapkg_total = arm_datalen_total/0x1EA;

		uint32_t curOffset = 0;

		memcpy(arm_databuf+curOffset, srlBuf+arm9off, arm9cpLen);
		curOffset += arm9cpLen;
		if(arm9cpLen < arm9len)
		{	//Add extra ARM9 Block to fill
			memcpy(arm_databuf+curOffset, srlBuf+arm9off+arm9cpLen-0x1EA, 0x1EA);
			memcpy(arm_databuf+curOffset, srlBuf+arm9off+arm9cpLen, arm9len-arm9cpLen);
			curOffset += 0x1EA;
		}

		memcpy(arm_databuf+curOffset, srlBuf+arm7off, arm7cpLen);
		curOffset += arm7cpLen;
		if(arm7cpLen < arm7len)
		{	//Add extra ARM7 Block to fill
			memcpy(arm_databuf+curOffset, srlBuf+arm7off+arm7cpLen-0x1EA, 0x1EA);
			memcpy(arm_databuf+curOffset, srlBuf+arm7off+arm7cpLen, arm7len-arm7cpLen);
			curOffset += 0x1EA;
		}
		//Verify Header CRC16
		wd_hdr_valid = dsVerifyHdr();
		//Get Header Total ROM Length
		memcpy(&tmp, srlHdr+0x80, 4);
		uint32_t romlen = __builtin_bswap32(tmp);
		//Signed ROMs always have a section after the ROM that starts with the string "ac"
		wd_has_rsa = (romlen+0x88 <= srlSize && srlBuf[romlen] == 0x61 && srlBuf[romlen+1] == 0x63);
		if(wd_has_rsa) memcpy(srlRSA, srlBuf+romlen, 0x88);
		//Set start state
		wd_state = WD_STATE_DSWAIT;

		printf("\nStarting WD...");
		//WD_Startup
		__wd_fd = WD_Init(DSCommunications);
		if(__wd_fd < 0)	printf("WD_Init: 0x%x\n", __wd_fd);
		printf("Done.");

		WD_Config conf __attribute__((aligned(32))) = {0};

		conf.mpParent.connectionTimeout = 4; //Timeout 4s?
		conf.mpParent.beaconPeriod = 0xC8; //beacon period 200ms
		conf.mpParent.maxNodes = 0xF; //max 15 nodes

		uint64_t mask __attribute__((aligned(32))) = 0x0003007F00000000; //default cfg mask
		printf("\nSetting Config...");
		ret = WD_SetConfig(&conf, mask);
		if(ret < 0)	printf("WD_SetConfig=0x%x\n", ret);
		printf("Done.");

		//WD_StartBeacon
		uint16_t beaconIn = (uint16_t)(ticks_to_microsecs(gettick())/64);

		memset(wdGameInfo, 0, 0x500);

		WD_GameInfo *ginfo = (WD_GameInfo*)wdGameInfo;

		//Set Start Beacon Data, no clue what all these values mean
		ginfo->base.header = 0x01000108;
		//DS Download Station GGID
		ginfo->base.GGID = 0x20014000;
		//TGID, random every host
		uint16_t rval = gettick();
		ginfo->base.TGID = (rval>>8) | (rval&0xFF);
		//more unkown values, appear to be similar to first set

		wdGameInfo[0xC] = 0xF0; wdGameInfo[0xD] = 1; wdGameInfo[0xE] = 8;
		printf("\nStarting beacon");
		ret = WD_ChangeBeacon(beaconIn, wdGameInfo, 0x80);
		if(ret < 0)	printf("WD_StartBeacon=0x%x\n", ret);
		//Beacon size
		ginfo->base.BeaconSize = 0x70;
		//Beacon type
		ginfo->base.BeaconType = 3;
		//DS Download Station GGID (again)
		ginfo->base.GGID_copy = 0x20014000;

		ret = WD_SetLinkState(1);
		if(ret < 0)	printf("WD_SetLinkState=0x%x\n", ret);

		//WD_GetLinkState
		do {
			ret = WD_GetLinkState();
		} while(ret == 0);
		if(ret != 1) printf("WD_GetLinkState=0x%x\n", ret);

		//Set up rest of Beacon Data
		memcpy(&tmp, srlHdr+0x68, 4);
		uint32_t iOff = __builtin_bswap32(tmp);
		const uint8_t *pBin;
		const uint8_t *cBin;
		if(wd_haxxstation)
		{
			pBin = tmpWdIconBuf;
			cBin = tmpWdIconBuf+0x20;
		}
		else
		{
			pBin = srlBuf+iOff+0x220;
			cBin = srlBuf+iOff+0x20;
		}
		//Set up Beacon PALETTE and CHAR Data from ROM
		memcpy(ginfo->palette_data, pBin, 0x20);
		memcpy(ginfo->character_data, cBin, 0x42);
		memcpy(ginfo->character_data_1, cBin+0x42, 0x62);
		memcpy(ginfo->character_data_2, cBin+0xA4, 0x62);
		memcpy(ginfo->character_data_3, cBin+0x106, 0x62);
		memcpy(ginfo->character_data_4, cBin+0x168, 0x62);
		memcpy(ginfo->character_data_5, cBin+0x1CA, 0x36);
		//Sender DS Name: FIX94
		ginfo->sendername_len = 0x5;
		u8strtou16("Ab221", ginfo->sendername, 5);
		//Max Players Allowed
		ginfo->maxplayersallowed = 1 << 8;
		u8strtou16("DSCom Test", ginfo->gamename, 0xA);

		//Description: Hi.
		//u8strtou16("Wsp", ginfo->gamedesc, 0xA);
		wdGameInfo[0x36A] = 0x48;
		wdGameInfo[0x36C] = 0x69;
		wdGameInfo[0x36E] = 0x2E;

		//Set up all sequence infos
		WD_GameInfBase base;
		memcpy(&base, wdGameInfo, sizeof(WD_GameInfBase));
		memset(wdGameInfo, 0, sizeof(WD_GameInfBase));

		for(i = 0; i < 10; i++)
		{
			WD_GameInfBase *cInfPtr = (WD_GameInfBase*)(wdGameInfo+(i<<7));
			memcpy(cInfPtr, &base, 0x1E);
			if(i == 9) //sequence end
				cInfPtr->sequence_end = 2;
			//current sequence
			cInfPtr->current_sequence = i;
			if(i < 9)
			{
				//current sequence
				cInfPtr->unk2 = i;
				//total sequences
				cInfPtr->total_sequences = 9;
			}
			else //number of players connected
				cInfPtr->unk2 = 0;
			//set payload len
			if(i < 8)
				cInfPtr->payload_len = 0x62;
			else if(i == 8)
				cInfPtr->payload_len = 0x48;
			else
				cInfPtr->payload_len = 1;
			int j;
			//gen checksum
			uint32_t chk = 0;
			for(j = 0x1A; j < 0x80; j+=2)
			{
				uint16_t cV = *(uint16_t*)(((uint8_t*)cInfPtr)+j);
				chk+=cV;
			}
			chk=0xFFFF&(~(chk+(chk/0x10000)));
			cInfPtr->checksum = chk;
		}

		//MPDLStartup Threads
		mpdl_active = true;
		beaconActive = true;
		//Beacon Thread
		LWP_CreateThread(&mpdl_thread_ptr,mpdl_thread,NULL,mpdl_stack,STACKSIZE,0x40);
		//Status Thread
		LWP_CreateThread(&mpdl_inf_thread_ptr,mpdl_inf_thread,NULL,mpdl_inf_stack,STACKSIZE,0x40);
		//Data Receive Thread
		LWP_CreateThread(&mpdl_recv_thread_ptr,mpdl_recv_thread,NULL,mpdl_recv_stack,STACKSIZE,0x80);
		//Data Send Thread
		LWP_CreateThread(&mpdl_send_thread_ptr,mpdl_send_thread,NULL,mpdl_send_stack,STACKSIZE,0x80);

		inited = true;

		while(1)
		{
			PAD_ScanPads();
			WPAD_ScanPads();
			if (PAD_ButtonsDown(0) || PAD_ButtonsHeld(0) || 
				WPAD_ButtonsDown(0) || WPAD_ButtonsHeld(0))
				break;
			printmain();
			printstatus();

			VIDEO_WaitVSync();
			VIDEO_WaitVSync();
		}
		printf("Button pressed, Cleanup\n");

		//MPDLCleanup Threads
		mpdl_active = false;

		//Data Send Thread
		LWP_JoinThread(mpdl_send_thread_ptr, NULL);
		//Data Receive Thread
		LWP_JoinThread(mpdl_recv_thread_ptr, NULL);
		//Status Thread
		LWP_JoinThread(mpdl_inf_thread_ptr, NULL);
		//Beacon Thread
		LWP_JoinThread(mpdl_thread_ptr, NULL);

		//WD_Cleanup
		WD_Deinit();

		if(wd_haxxstation)
		{
			ndsfile_haxx_end();
			demodatabuf = NULL;
			wd_haxxstation = false;
		}
	}

	//free all buffers at once
	free(clientBuf);
	free(srlBuf);
	free(arm_databuf);
	free(names);

	//No need for LZO anymore
	ndsfile_demomenu_end();

	NCD_UnlockWirelessDriver(lockid);

	printf("All done, Exit\n");

	WPAD_Shutdown();

	VIDEO_WaitVSync();
	VIDEO_WaitVSync();

	return 0;
}
