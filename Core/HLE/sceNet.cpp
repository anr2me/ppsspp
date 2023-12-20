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

#if defined(_WIN32)
#include "Common/CommonWindows.h" // Needed for std::max/min to works
#endif

#if __linux__ || __APPLE__ || defined(__OpenBSD__)
#include <unistd.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <netinet/tcp.h>
#include <fcntl.h>
#endif

#ifndef MSG_NOSIGNAL
// Default value to 0x00 (do nothing) in systems where it's not supported.
#define MSG_NOSIGNAL 0x00
#endif

#include "Common/Net/Resolve.h"
#include "Common/Data/Text/Parsers.h"

#include "Common/Serialize/Serializer.h"
#include "Common/Serialize/SerializeFuncs.h"
#include "Common/Serialize/SerializeMap.h"
#include "Core/HLE/HLE.h"
#include "Core/HLE/FunctionWrappers.h"
#include "Core/HLE/sceKernelMemory.h"
#include "Core/MIPS/MIPS.h"
#include "Core/Config.h"
#include "Core/System.h"
#include "Core/ELF/ParamSFO.h"
#include "Core/MemMapHelpers.h"
#include "Core/Util/PortManager.h"

#include "sceKernel.h"
#include "sceKernelThread.h"
#include "sceKernelMutex.h"
#include "sceUtility.h"

#include "Core/HLE/proAdhoc.h"
#include "Core/HLE/sceNetAdhoc.h"
#include "Core/HLE/sceNet.h"
#include "Core/HLE/sceNp.h"
#include "Core/HLE/sceNp2.h"
#include "Core/Reporting.h"
#include "Core/Instance.h"

#if PPSSPP_PLATFORM(SWITCH) && !defined(INADDR_NONE)
// Missing toolchain define
#define INADDR_NONE 0xFFFFFFFF
#endif

bool netInited;
bool netInetInited;

u32 netDropRate = 0;
u32 netDropDuration = 0;
u32 netPoolAddr = 0;
u32 netThread1Addr = 0;
u32 netThread2Addr = 0;

static struct SceNetMallocStat netMallocStat = {};

static std::map<int, NetResolver> netResolvers;

static std::map<int, ApctlHandler> apctlHandlers;

std::string defaultNetConfigName = "NetConf";
std::string defaultNetSSID = "Wifi"; // fake AP/hotspot
int netApctlInfoId = 0;
SceNetApctlInfoInternal netApctlInfo;

bool netApctlInited;
u32 netApctlState;
u32 apctlProdCodeAddr = 0;
u32 apctlThreadHackAddr = 0;
u32_le apctlThreadCode[3];
SceUID apctlThreadID = 0;
int apctlStateEvent = -1;
int actionAfterApctlMipsCall;
std::recursive_mutex apctlEvtMtx;
std::deque<ApctlArgs> apctlEvents;

// TODO: Combine AdhocSocket class and InetSocket class into a single class just like kernelObjects, where Port Offset will be handled internally, and can also be used for future feature (ie. tunneling)
//PSPSocketPool pspSockets; // Keep tracks connection state and nonblocking mode (which is required to simulate blocking mode)
int inetLastErrno = 0; // TODO: since errno can only be read once, we should keep track the value to be used on sceNetInetGetErrno
int inetLastSocket = -1; // A workaround to keep the most recent socket id for sceNetInetSelect, until we have a socket class wrapper

u32 Net_Term();
int NetApctl_Term();
void NetApctl_InitDefaultInfo();
void NetApctl_InitInfo(int confId);

void AfterApctlMipsCall::DoState(PointerWrap & p) {
	auto s = p.Section("AfterApctlMipsCall", 1, 1);
	if (!s)
		return;
	// Just in case there are "s" corruption in the future where s.ver is a negative number
	if (s >= 1) {
		Do(p, handlerID);
		Do(p, oldState);
		Do(p, newState);
		Do(p, event);
		Do(p, error);
		Do(p, argsAddr);
	} else {
		handlerID = -1;
		oldState = 0;
		newState = 0;
		event = 0;
		error = 0;
		argsAddr = 0;
	}
}

void AfterApctlMipsCall::run(MipsCall& call) {
	u32 v0 = currentMIPS->r[MIPS_REG_V0];
	DEBUG_LOG(SCENET, "AfterApctlMipsCall::run [ID=%i][OldState=%d][NewState=%d][Event=%d][Error=%d][ArgsPtr=%08x] [cbId: %u][retV0: %08x]", handlerID, oldState, newState, event, error, argsAddr, call.cbId, v0);
	//call.setReturnValue(v0);
}

void AfterApctlMipsCall::SetData(int HandlerID, int OldState, int NewState, int Event, int Error, u32_le ArgsAddr) {
	handlerID = HandlerID;
	oldState = OldState;
	newState = NewState;
	event = Event;
	error = Error;
	argsAddr = ArgsAddr;
}

void InitLocalhostIP() {
	// The entire 127.*.*.* is reserved for loopback.
	uint32_t localIP = 0x7F000001 + PPSSPP_ID - 1;

	g_localhostIP.in.sin_family = AF_INET;
	g_localhostIP.in.sin_addr.s_addr = htonl(localIP);
	g_localhostIP.in.sin_port = 0;

	std::string serverStr = StripSpaces(g_Config.proAdhocServer);
	isLocalServer = (!strcasecmp(serverStr.c_str(), "localhost") || serverStr.find("127.") == 0);
}

static void __ApctlState(u64 userdata, int cyclesLate) {
	SceUID threadID = userdata >> 32;
	int uid = (int)(userdata & 0xFFFFFFFF);
	int event = uid - 1;

	s64 result = 0;
	u32 error = 0;

	SceUID waitID = __KernelGetWaitID(threadID, WAITTYPE_NET, error);
	if (waitID == 0 || error != 0) {
		WARN_LOG(SCENET, "sceNetApctl State WaitID(%i) on Thread(%i) already woken up? (error: %08x)", uid, threadID, error);
		return;
	}

	u32 waitVal = __KernelGetWaitValue(threadID, error);
	if (error == 0) {
		netApctlState = waitVal;
	}

	__KernelResumeThreadFromWait(threadID, result);
	DEBUG_LOG(SCENET, "Returning (WaitID: %d, error: %08x) Result (%08x) of sceNetApctl - Event: %d, State: %d", waitID, error, (int)result, event, netApctlState);
}

// Used to change Apctl State after a delay and before executing callback mipscall (since we don't have beforeAction)
int ScheduleApctlState(int event, int newState, int usec, const char* reason) {
	int uid = event + 1;

	u64 param = ((u64)__KernelGetCurThread()) << 32 | uid;
	CoreTiming::ScheduleEvent(usToCycles(usec), apctlStateEvent, param);
	__KernelWaitCurThread(WAITTYPE_NET, uid, newState, 0, false, reason);

	return 0;
}

void __NetApctlInit() {
	netApctlInited = false;
	netApctlState = PSP_NET_APCTL_STATE_DISCONNECTED;
	apctlStateEvent = CoreTiming::RegisterEvent("__ApctlState", __ApctlState);
	apctlHandlers.clear();
	apctlEvents.clear();
	NetApctl_InitDefaultInfo();
}

static void __ResetInitNetLib() {
	netInited = false;
	netInetInited = false;

	memset(&netMallocStat, 0, sizeof(netMallocStat));
	memset(&parameter, 0, sizeof(parameter));
}

void __NetCallbackInit() {
	// Init Network Callbacks
	dummyThreadHackAddr = __CreateHLELoop(dummyThreadCode, "sceNetAdhoc", "__NetTriggerCallbacks", "dummythreadhack");
	matchingThreadHackAddr = __CreateHLELoop(matchingThreadCode, "sceNetAdhocMatching", "__NetMatchingCallbacks", "matchingThreadHack");
	apctlThreadHackAddr = __CreateHLELoop(apctlThreadCode, "sceNetApctl", "__NetApctlCallbacks", "apctlThreadHack");

	// Newer one should be placed last to prevent callbacks going to the wrong after action after loading from old save state
	actionAfterMatchingMipsCall = __KernelRegisterActionType(AfterMatchingMipsCall::Create);
	actionAfterAdhocMipsCall = __KernelRegisterActionType(AfterAdhocMipsCall::Create);
	actionAfterApctlMipsCall = __KernelRegisterActionType(AfterApctlMipsCall::Create);
}

void __NetResolverInit() {
	netResolvers.clear();
}

void __NetInit() {
	// Windows: Assuming WSAStartup already called beforehand
	portOffset = g_Config.iPortOffset;
	isOriPort = g_Config.bEnableUPnP && g_Config.bUPnPUseOriginalPort;
	minSocketTimeoutUS = g_Config.iMinTimeout * 1000UL;

	// Init Default AdhocServer struct
	g_adhocServerIP.in.sin_family = AF_INET;
	g_adhocServerIP.in.sin_port = htons(SERVER_PORT); //27312 // Maybe read this from config too
	g_adhocServerIP.in.sin_addr.s_addr = INADDR_NONE;

	dummyPeekBuf64k = (char*)malloc(dummyPeekBuf64kSize);
	InitLocalhostIP();

	SceNetEtherAddr mac;
	getLocalMac(&mac);
	INFO_LOG(SCENET, "LocalHost IP will be %s [%s]", ip2str(g_localhostIP.in.sin_addr).c_str(), mac2str(&mac).c_str());
	
	// TODO: May be we should initialize & cleanup somewhere else than here for PortManager to be used as general purpose for whatever port forwarding PPSSPP needed
	__UPnPInit();

	__ResetInitNetLib();
	__NetApctlInit();
	__NetCallbackInit();
	__NetResolverInit();
}

void __NetApctlShutdown() {
	if (apctlThreadHackAddr) {
		kernelMemory.Free(apctlThreadHackAddr);
		apctlThreadHackAddr = 0;
	}
	apctlHandlers.clear();
	apctlEvents.clear();
}

void __NetResolverShutdown() {
	netResolvers.clear();
}

void __NetShutdown() {
	// Network Cleanup
	Net_Term();

	__NetResolverShutdown();
	__NetApctlShutdown();
	__ResetInitNetLib();

	// Since PortManager supposed to be general purpose for whatever port forwarding PPSSPP needed, may be we shouldn't clear & restore ports in here? it will be cleared and restored by PortManager's destructor when exiting PPSSPP anyway
	__UPnPShutdown();

	free(dummyPeekBuf64k);
}

static void __UpdateApctlHandlers(u32 oldState, u32 newState, u32 flag, u32 error) {
	std::lock_guard<std::recursive_mutex> apctlGuard(apctlEvtMtx);
	apctlEvents.push_back({ oldState, newState, flag, error });
}

// Make sure MIPS calls have been fully executed before the next notifyApctlHandlers
void notifyApctlHandlers(int oldState, int newState, int flag, int error) {
	__UpdateApctlHandlers(oldState, newState, flag, error);
}

void netValidateLoopMemory() {
	// Allocate Memory if it wasn't valid/allocated after loaded from old SaveState
	if (!apctlThreadHackAddr || (apctlThreadHackAddr && strcmp("apctlThreadHack", kernelMemory.GetBlockTag(apctlThreadHackAddr)) != 0)) {
		u32 blockSize = sizeof(apctlThreadCode);
		apctlThreadHackAddr = kernelMemory.Alloc(blockSize, false, "apctlThreadHack");
		if (apctlThreadHackAddr) Memory::Memcpy(apctlThreadHackAddr, apctlThreadCode, sizeof(apctlThreadCode));
	}
}

// This feels like a dubious proposition, mostly...
void __NetDoState(PointerWrap &p) {
	auto s = p.Section("sceNet", 1, 6);
	if (!s)
		return;

	auto cur_netInited = netInited;
	auto cur_netInetInited = netInetInited;
	auto cur_netApctlInited = netApctlInited;

	Do(p, netInited);
	Do(p, netInetInited);
	Do(p, netApctlInited);
	Do(p, apctlHandlers);
	Do(p, netMallocStat);
	if (s < 2) {
		netDropRate = 0;
		netDropDuration = 0;
	} else {
		Do(p, netDropRate);
		Do(p, netDropDuration);
	}
	if (s < 3) {
		netPoolAddr = 0;
		netThread1Addr = 0;
		netThread2Addr = 0;
	} else {
		Do(p, netPoolAddr);
		Do(p, netThread1Addr);
		Do(p, netThread2Addr);
	}
	if (s >= 4) {
		Do(p, netApctlState);
		Do(p, netApctlInfo);
		Do(p, actionAfterApctlMipsCall);
		if (actionAfterApctlMipsCall != -1) {
			__KernelRestoreActionType(actionAfterApctlMipsCall, AfterApctlMipsCall::Create);
		}
		Do(p, apctlThreadHackAddr);
		Do(p, apctlThreadID);
	}
	else {
		actionAfterApctlMipsCall = -1;
		apctlThreadHackAddr = 0;
		apctlThreadID = 0;
	}
	if (s >= 5) {
		Do(p, apctlStateEvent);
	} else {
		apctlStateEvent = -1;
	}
	CoreTiming::RestoreRegisterEvent(apctlStateEvent, "__ApctlState", __ApctlState);
	if (s >= 6) {
		Do(p, netApctlInfoId);
		Do(p, netApctlInfo);
	}
	else {
		netApctlInfoId = 0;
		NetApctl_InitDefaultInfo();
	}

	if (p.mode == p.MODE_READ) {
		// Let's not change "Inited" value when Loading SaveState in the middle of multiplayer to prevent memory & port leaks
		netApctlInited = cur_netApctlInited;
		netInetInited = cur_netInetInited;
		netInited = cur_netInited;

		// Discard leftover events
		apctlEvents.clear();
		// Discard created resolvers for now (since i'm not sure whether the information in the struct is sufficient or not, and we don't support multi-threading yet anyway)
		netResolvers.clear();
	}
}

template <typename I> std::string num2hex(I w, size_t hex_len) {
	static const char* digits = "0123456789ABCDEF";
	std::string rc(hex_len, '0');
	for (size_t i = 0, j = (hex_len - 1) * 4; i < hex_len; ++i, j -= 4)
		rc[i] = digits[(w >> j) & 0x0f];
	return rc;
}

std::string error2str(u32 errorCode) {
	std::string str = "";
	if (((errorCode >> 31) & 1) != 0)
		str += "ERROR ";
	if (((errorCode >> 30) & 1) != 0)
		str += "CRITICAL ";
	switch ((errorCode >> 16) & 0xfff) {
	case 0x41:
		str += "NET ";
		break;
	default:
		str += "UNK"+num2hex(u16((errorCode >> 16) & 0xfff), 3)+" ";
	}
	switch ((errorCode >> 8) & 0xff) {
	case 0x00:
		str += "COMMON ";
		break;
	case 0x01:
		str += "CORE ";
		break;
	case 0x02:
		str += "INET ";
		break;
	case 0x03:
		str += "POECLIENT ";
		break;
	case 0x04:
		str += "RESOLVER ";
		break;
	case 0x05:
		str += "DHCP ";
		break;
	case 0x06:
		str += "ADHOC_AUTH ";
		break;
	case 0x07:
		str += "ADHOC ";
		break;
	case 0x08:
		str += "ADHOC_MATCHING ";
		break;
	case 0x09:
		str += "NETCNF ";
		break;
	case 0x0a:
		str += "APCTL ";
		break;
	case 0x0b:
		str += "ADHOCCTL ";
		break;
	case 0x0c:
		str += "UNKNOWN1 ";
		break;
	case 0x0d:
		str += "WLAN ";
		break;
	case 0x0e:
		str += "EAPOL ";
		break;
	case 0x0f:
		str += "8021x ";
		break;
	case 0x10:
		str += "WPA ";
		break;
	case 0x11:
		str += "UNKNOWN2 ";
		break;
	case 0x12:
		str += "TRANSFER ";
		break;
	case 0x13:
		str += "ADHOC_DISCOVER ";
		break;
	case 0x14:
		str += "ADHOC_DIALOG ";
		break;
	case 0x15:
		str += "WISPR ";
		break;
	default:
		str += "UNKNOWN"+num2hex(u8((errorCode >> 8) & 0xff))+" ";
	}
	str += num2hex(u8(errorCode & 0xff));
	return str;
}

int getNonBlockingFlag(int sock) {
#ifdef _WIN32
	// Windows can't retrieve nonblocking status
	return 0;
#else
	int sockflag = fcntl(sock, F_GETFL, O_NONBLOCK);
	// Fixme: O_NONBLOCK is defined but broken on SunOS 4.1.x and AIX 3.2.5.
	if (sockflag == -1)
		sockflag = 0;
	return sockflag & O_NONBLOCK;
#endif
}

void __NetApctlCallbacks()
{
	std::lock_guard<std::recursive_mutex> apctlGuard(apctlEvtMtx);
	std::lock_guard<std::recursive_mutex> npAuthGuard(npAuthEvtMtx);
	std::lock_guard<std::recursive_mutex> npMatching2Guard(npMatching2EvtMtx);
	hleSkipDeadbeef();
	int delayus = 10000;

	// We are temporarily borrowing APctl thread for NpAuth callbacks for testing to simulate authentication
	if (!npAuthEvents.empty())
	{
		auto& args = npAuthEvents.front();
		auto& id = args.data[0];
		auto& result = args.data[1];
		auto& argAddr = args.data[2];
		npAuthEvents.pop_front();

		delayus = (adhocEventDelay + adhocExtraDelay);

		int handlerID = id - 1;
		for (std::map<int, NpAuthHandler>::iterator it = npAuthHandlers.begin(); it != npAuthHandlers.end(); ++it) {
			if (it->first == handlerID) {
				DEBUG_LOG(SCENET, "NpAuthCallback [HandlerID=%i][RequestID=%d][Result=%d][ArgsPtr=%08x]", it->first, id, result, it->second.argument);
				// TODO: Update result / args.data[1] with the actual ticket length (or error code?)
				hleEnqueueCall(it->second.entryPoint, 3, args.data);
			}
		}
	}

	// Temporarily borrowing APctl thread for NpMatching2 callbacks for testing purpose
	if (!npMatching2Events.empty())
	{
		auto& args = npMatching2Events.front();
		auto& event = args.data[0];
		auto& stat = args.data[1];
		auto& serverIdPtr = args.data[2];
		auto& inStructPtr = args.data[3];
		auto& newStat = args.data[5];
		npMatching2Events.pop_front();

		delayus = (adhocEventDelay + adhocExtraDelay);

		//int handlerID = id - 1;
		for (std::map<int, NpMatching2Handler>::iterator it = npMatching2Handlers.begin(); it != npMatching2Handlers.end(); ++it) {
			//if (it->first == handlerID) 
			{
				DEBUG_LOG(SCENET, "NpMatching2Callback [HandlerID=%i][EventID=%04x][State=%04x][ArgsPtr=%08x]", it->first, event, stat, it->second.argument);
				hleEnqueueCall(it->second.entryPoint, 7, args.data);
			}
		}
		// Per npMatching2 function callback
		u32* inStruct = (u32*)Memory::GetPointer(inStructPtr);
		if (Memory::IsValidAddress(inStruct[0])) {
			DEBUG_LOG(SCENET, "NpMatching2Callback [ServerID=%i][EventID=%04x][State=%04x][FuncAddr=%08x][ArgsPtr=%08x]", *(u32*)Memory::GetPointer(serverIdPtr), event, stat, inStruct[0], inStruct[1]);
			hleEnqueueCall(inStruct[0], 7, args.data);
		}
	}

	// How AP works probably like this: Game use sceNetApctl function -> sceNetApctl let the hardware know and do their's thing and have a new State -> Let the game know the resulting State through Event on their handler
	if (!apctlEvents.empty())
	{
		auto& args = apctlEvents.front();
		auto& oldState = args.data[0];
		auto& newState = args.data[1];
		auto& event = args.data[2];
		auto& error = args.data[3];
		apctlEvents.pop_front();

		// Adjust delay according to current event.
		if (event == PSP_NET_APCTL_EVENT_CONNECT_REQUEST || event == PSP_NET_APCTL_EVENT_GET_IP || event == PSP_NET_APCTL_EVENT_SCAN_REQUEST || event == PSP_NET_APCTL_EVENT_ESTABLISHED)
			delayus = adhocEventDelay;
		else
			delayus = adhocEventPollDelay;

		// Do we need to change the oldState? even if there was error?
		if (error == 0) 
		{
			//oldState = netApctlState;
			netApctlState = newState;
		}

		// Need to make sure netApctlState is updated before calling the callback's mipscall so the game can GetState()/GetInfo() within their handler's subroutine and make use the new State/Info
		// Should we update NewState & Error accordingly to Event before executing the mipscall ? sceNetApctl* functions might want to set the error value tho, so we probably should leave it untouched, right?
		//error = 0;
		switch (event) {
		case PSP_NET_APCTL_EVENT_CONNECT_REQUEST:
			newState = PSP_NET_APCTL_STATE_JOINING; // Should we set the State to PSP_NET_APCTL_STATE_DISCONNECTED if there was error?
			if (error != 0) 
				apctlEvents.push_front({ oldState, PSP_NET_APCTL_STATE_DISCONNECTED, PSP_NET_APCTL_EVENT_ERROR, error });
			else
				apctlEvents.push_front({ oldState, newState, PSP_NET_APCTL_EVENT_ESTABLISHED, 0 }); // Should we use PSP_NET_APCTL_EVENT_EAP_AUTH if securityType is not NONE?
			break;

		case PSP_NET_APCTL_EVENT_ESTABLISHED:
			newState = PSP_NET_APCTL_STATE_GETTING_IP;
			// FIXME: Official prx seems to return ERROR 0x80410280 on the next event when using invalid connection profile to Connect?
			if (error != 0) 
				apctlEvents.push_front({ oldState, PSP_NET_APCTL_STATE_DISCONNECTED, PSP_NET_APCTL_EVENT_ERROR, error });
			else 
				apctlEvents.push_front({ oldState, newState, PSP_NET_APCTL_EVENT_GET_IP, 0 });
			break;

		case PSP_NET_APCTL_EVENT_GET_IP:
			newState = PSP_NET_APCTL_STATE_GOT_IP;
			NetApctl_InitInfo(netApctlInfoId);
			break;

		case PSP_NET_APCTL_EVENT_DISCONNECT_REQUEST:
			newState = PSP_NET_APCTL_STATE_DISCONNECTED;
			delayus = adhocDefaultDelay / 2; // FIXME: Similar to Adhocctl Disconnect, we probably need to change the state within a frame-time (or less to be safer)
			break;

		case PSP_NET_APCTL_EVENT_SCAN_REQUEST:
			newState = PSP_NET_APCTL_STATE_SCANNING;
			if (error != 0) 
				apctlEvents.push_front({ oldState, PSP_NET_APCTL_STATE_DISCONNECTED, PSP_NET_APCTL_EVENT_ERROR, error });
			else
				apctlEvents.push_front({ oldState, newState, PSP_NET_APCTL_EVENT_SCAN_COMPLETE, 0 });
			break;

		case PSP_NET_APCTL_EVENT_SCAN_COMPLETE:
			newState = PSP_NET_APCTL_STATE_DISCONNECTED;
			if (error == 0)
				apctlEvents.push_front({ oldState, newState, PSP_NET_APCTL_EVENT_SCAN_STOP, 0 });
			break;

		case PSP_NET_APCTL_EVENT_SCAN_STOP:
			newState = PSP_NET_APCTL_STATE_DISCONNECTED;
			break;

		case PSP_NET_APCTL_EVENT_EAP_AUTH: // Is this suppose to happen between JOINING and ESTABLISHED ?
			newState = PSP_NET_APCTL_STATE_EAP_AUTH;
			if (error != 0)
				apctlEvents.push_front({ oldState, PSP_NET_APCTL_STATE_DISCONNECTED, PSP_NET_APCTL_EVENT_ERROR, error });
			else
				apctlEvents.push_front({ oldState, newState, PSP_NET_APCTL_EVENT_KEY_EXCHANGE, 0 }); // not sure if KEY_EXCHANGE is the next step after AUTH or not tho
			break;

		case PSP_NET_APCTL_EVENT_KEY_EXCHANGE: // Is this suppose to happen between JOINING and ESTABLISHED ?
			newState = PSP_NET_APCTL_STATE_KEY_EXCHANGE;
			if (error != 0)
				apctlEvents.push_front({ oldState, PSP_NET_APCTL_STATE_DISCONNECTED, PSP_NET_APCTL_EVENT_ERROR, error });
			else
				apctlEvents.push_front({ oldState, newState, PSP_NET_APCTL_EVENT_ESTABLISHED, 0 });
			break;

		case PSP_NET_APCTL_EVENT_RECONNECT:
			newState = PSP_NET_APCTL_STATE_DISCONNECTED;
			if (error != 0)
				apctlEvents.push_front({ oldState, PSP_NET_APCTL_STATE_DISCONNECTED, PSP_NET_APCTL_EVENT_ERROR, error });
			else
				apctlEvents.push_front({ oldState, newState, PSP_NET_APCTL_EVENT_CONNECT_REQUEST, 0 });
			break;

		case PSP_NET_APCTL_EVENT_ERROR:
			newState = PSP_NET_APCTL_STATE_DISCONNECTED;
			break;
		}
		// Do we need to change the newState? even if there were error?
		//if (error != 0)
		//	newState = netApctlState;

		// Since 0 is a valid index to types_ we use -1 to detects if it was loaded from an old save state
		if (actionAfterApctlMipsCall < 0) {
			actionAfterApctlMipsCall = __KernelRegisterActionType(AfterApctlMipsCall::Create);
		}

		// Run mipscall. Should we skipped executing the mipscall if oldState == newState? 
		for (std::map<int, ApctlHandler>::iterator it = apctlHandlers.begin(); it != apctlHandlers.end(); ++it) {
			DEBUG_LOG(SCENET, "ApctlCallback [ID=%i][OldState=%d][NewState=%d][Event=%d][Error=%08x][ArgsPtr=%08x]", it->first, oldState, newState, event, error, it->second.argument);
			args.data[4] = it->second.argument;
			AfterApctlMipsCall* after = (AfterApctlMipsCall*)__KernelCreateAction(actionAfterApctlMipsCall);
			after->SetData(it->first, oldState, newState, event, error, it->second.argument);
			hleEnqueueCall(it->second.entryPoint, 5, args.data, after);
		}
		// Similar to Adhocctl, new State might need to be set after delayed, right before executing the mipscall (ie. simulated beforeAction)
		ScheduleApctlState(event, newState, delayus, "apctl callback state");
		return;
	}

	// Must be delayed long enough whenever there is a pending callback to make sure previous callback & it's afterAction are fully executed
	sceKernelDelayThread(delayus);
}

static inline u32 AllocUser(u32 size, bool fromTop, const char *name) {
	u32 addr = userMemory.Alloc(size, fromTop, name);
	if (addr == -1)
		return 0;
	return addr;
}

static inline void FreeUser(u32 &addr) {
	if (addr != 0)
		userMemory.Free(addr);
	addr = 0;
}

u32 Net_Term() {
	// May also need to Terminate netAdhocctl and netAdhoc to free some resources & threads, since the game (ie. GTA:VCS, Wipeout Pulse, etc) might not called them before calling sceNetTerm and causing them to behave strangely on the next sceNetInit & sceNetAdhocInit
	NetAdhocctl_Term();
	NetAdhoc_Term();

	// TODO: Not implemented yet
	NetApctl_Term();
	//NetInet_Term();

	// Library is initialized
	if (netInited) {
		// Delete Adhoc Sockets
		deleteAllAdhocSockets();

		// Delete GameMode Buffer
		//deleteAllGMB();

		// Terminate Internet Library
		//sceNetInetTerm();

		// Unload Internet Modules (Just keep it in memory... unloading crashes?!)
		// if (_manage_modules != 0) sceUtilityUnloadModule(PSP_MODULE_NET_INET);
		// Library shutdown
	}

	FreeUser(netPoolAddr);
	FreeUser(netThread1Addr);
	FreeUser(netThread2Addr);
	netInited = false;

	return 0;
}

static u32 sceNetTerm() {
	WARN_LOG(SCENET, "sceNetTerm() at %08x", currentMIPS->pc);
	int retval = Net_Term();

	// Give time to make sure everything are cleaned up
	hleEatMicro(adhocDefaultDelay);
	return retval;
}

/*
Parameters:
	poolsize	- Memory pool size (appears to be for the whole of the networking library).
	calloutprio	- Priority of the SceNetCallout thread.
	calloutstack	- Stack size of the SceNetCallout thread (defaults to 4096 on non 1.5 firmware regardless of what value is passed).
	netintrprio	- Priority of the SceNetNetintr thread.
	netintrstack	- Stack size of the SceNetNetintr thread (defaults to 4096 on non 1.5 firmware regardless of what value is passed).
*/
static int sceNetInit(u32 poolSize, u32 calloutPri, u32 calloutStack, u32 netinitPri, u32 netinitStack)  {
	// TODO: Create Network Threads using given priority & stack
	// TODO: The correct behavior is actually to allocate more and leak the other threads/pool.
	// But we reset here for historic reasons (GTA:VCS potentially triggers this.)
	if (netInited)
		Net_Term(); // This cleanup attempt might not worked when SaveState were loaded in the middle of multiplayer game and re-entering multiplayer, thus causing memory leaks & wasting binded ports. May be we shouldn't save/load "Inited" vars on SaveState?

	if (poolSize == 0) {
		return hleLogError(SCENET, SCE_KERNEL_ERROR_ILLEGAL_MEMSIZE, "invalid pool size");
	} else if (calloutPri < 0x08 || calloutPri > 0x77) {
		return hleLogError(SCENET, SCE_KERNEL_ERROR_ILLEGAL_PRIORITY, "invalid callout thread priority");
	} else if (netinitPri < 0x08 || netinitPri > 0x77) {
		return hleLogError(SCENET, SCE_KERNEL_ERROR_ILLEGAL_PRIORITY, "invalid init thread priority");
	}

	// TODO: Should also start the threads, probably?  For now, let's just allocate.
	// TODO: Respect the stack size if firmware set to 1.50?
	u32 stackSize = 4096;
	netThread1Addr = AllocUser(stackSize, true, "netstack1");
	if (netThread1Addr == 0) {
		return hleLogError(SCENET, SCE_KERNEL_ERROR_NO_MEMORY, "unable to allocate thread");
	}
	netThread2Addr = AllocUser(stackSize, true, "netstack2");
	if (netThread2Addr == 0) {
		FreeUser(netThread1Addr);
		return hleLogError(SCENET, SCE_KERNEL_ERROR_NO_MEMORY, "unable to allocate thread");
	}

	netPoolAddr = AllocUser(poolSize, false, "netpool");
	if (netPoolAddr == 0) {
		FreeUser(netThread1Addr);
		FreeUser(netThread2Addr);
		return hleLogError(SCENET, SCE_KERNEL_ERROR_NO_MEMORY, "unable to allocate pool");
	}

	WARN_LOG(SCENET, "sceNetInit(poolsize=%d, calloutpri=%i, calloutstack=%d, netintrpri=%i, netintrstack=%d) at %08x", poolSize, calloutPri, calloutStack, netinitPri, netinitStack, currentMIPS->pc);
	
	netMallocStat.pool = poolSize - 0x20; // On Vantage Master Portable this is slightly (32 bytes) smaller than the poolSize arg when tested with JPCSP + prx files
	netMallocStat.maximum = 0x4050; // Dummy maximum foot print
	netMallocStat.free = netMallocStat.pool; // Dummy free size, we should set this high enough to prevent any issue (ie. Vantage Master Portable), this is probably the only field being checked by games?

	// Clear Socket Translator Memory
	memset(&adhocSockets, 0, sizeof(adhocSockets));

	netInited = true;
	return hleLogSuccessI(SCENET, 0);
}

// Free(delete) thread info / data. 
// Normal usage: sceKernelDeleteThread followed by sceNetFreeThreadInfo with the same threadID as argument
static int sceNetFreeThreadinfo(SceUID thid) {
	ERROR_LOG(SCENET, "UNIMPL sceNetFreeThreadinfo(%i)", thid);

	return 0;
}

// Abort a thread.
static int sceNetThreadAbort(SceUID thid) {
	ERROR_LOG(SCENET, "UNIMPL sceNetThreadAbort(%i)", thid);

	return 0;
}

static u32 sceWlanGetEtherAddr(u32 addrAddr) {
	if (!Memory::IsValidRange(addrAddr, 6)) {
		// More correctly, it should crash.
		return hleLogError(SCENET, SCE_KERNEL_ERROR_ILLEGAL_ADDR, "illegal address");
	}

	u8 *addr = Memory::GetPointerWriteUnchecked(addrAddr);
	if (PPSSPP_ID > 1) {
		Memory::Memset(addrAddr, PPSSPP_ID, 6);
		// Making sure the 1st 2-bits on the 1st byte of OUI are zero to prevent issue with some games (ie. Gran Turismo)
		addr[0] &= 0xfc;
	} else {
		// Read MAC Address from config
		if (!ParseMacAddress(g_Config.sMACAddress, addr)) {
			ERROR_LOG(SCENET, "Error parsing mac address %s", g_Config.sMACAddress.c_str());
			Memory::Memset(addrAddr, 0, 6);
		}
	}
	NotifyMemInfo(MemBlockFlags::WRITE, addrAddr, 6, "WlanEtherAddr");

	return hleLogSuccessI(SCENET, hleDelayResult(0, "get ether mac", 200));
}

static u32 sceNetGetLocalEtherAddr(u32 addrAddr) {
	// FIXME: Return 0x80410180 (pspnet[_core] error code?) before successful attempt to Create/Connect/Join a Group? (ie. adhocctlCurrentMode == ADHOCCTL_MODE_NONE)
	if (adhocctlCurrentMode == ADHOCCTL_MODE_NONE && netApctlState == PSP_NET_APCTL_STATE_DISCONNECTED)
		return hleLogDebug(SCENET, 0x80410180, "address not available?");

	return sceWlanGetEtherAddr(addrAddr);
}

static u32 sceWlanDevIsPowerOn() {
	return hleLogSuccessVerboseI(SCENET, g_Config.bEnableWlan ? 1 : 0);
}

static u32 sceWlanGetSwitchState() {
	return hleLogSuccessVerboseI(SCENET, g_Config.bEnableWlan ? 1 : 0);
}

// Probably a void function, but often returns a useful value.
static void sceNetEtherNtostr(u32 macPtr, u32 bufferPtr) {
	DEBUG_LOG(SCENET, "sceNetEtherNtostr(%08x, %08x) at %08x", macPtr, bufferPtr, currentMIPS->pc);

	if (Memory::IsValidAddress(bufferPtr) && Memory::IsValidAddress(macPtr)) {
		char *buffer = (char *)Memory::GetPointerWriteUnchecked(bufferPtr);
		const u8 *mac = Memory::GetPointerUnchecked(macPtr);

		// MAC address is always 6 bytes / 48 bits.
		sprintf(buffer, "%02x:%02x:%02x:%02x:%02x:%02x",
			mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);

		VERBOSE_LOG(SCENET, "sceNetEtherNtostr - [%s]", buffer);
	}
}

static int hex_to_digit(int c) {
	if (c >= '0' && c <= '9')
		return c - '0';
	if (c >= 'a' && c <= 'f')
		return c - 'a' + 10;
	if (c >= 'A' && c <= 'F')
		return c - 'A' + 10;
	return -1;
}

// Probably a void function, but sometimes returns a useful-ish value.
static void sceNetEtherStrton(u32 bufferPtr, u32 macPtr) {
	DEBUG_LOG(SCENET, "sceNetEtherStrton(%08x, %08x)", bufferPtr, macPtr);

	if (Memory::IsValidAddress(bufferPtr) && Memory::IsValidAddress(macPtr)) {
		const char *buffer = (const char *)Memory::GetPointerUnchecked(bufferPtr);
		u8 *mac = Memory::GetPointerWrite(macPtr);

		// MAC address is always 6 pairs of hex digits.
		// TODO: Funny stuff happens if it's too short.
		u8 value = 0;
		for (int i = 0; i < 6 && *buffer != 0; ++i) {
			value = 0;

			int c = hex_to_digit(*buffer++);
			if (c != -1) {
				value |= c << 4;
			}
			c = hex_to_digit(*buffer++);
			if (c != -1) {
				value |= c;
			}

			*mac++ = value;

			// Skip a single character in between.
			// TODO: Strange behavior on the PSP, let's just null check.
			if (*buffer++ == 0) {
				break;
			}
		}

		VERBOSE_LOG(SCENET, "sceNetEtherStrton - [%s]", mac2str((SceNetEtherAddr*)Memory::GetPointer(macPtr)).c_str());
		// Seems to maybe kinda return the last value.  Probably returns void.
		//return value;
	}
}


int convertMsgFlagPSP2Host(int flag) {
	switch (flag) {
	case PSP_NET_INET_MSG_OOB:
		return MSG_OOB;
	case PSP_NET_INET_MSG_PEEK:
		return MSG_PEEK;
	case PSP_NET_INET_MSG_DONTROUTE:
		return MSG_DONTROUTE;
#if defined(MSG_EOR)
	case PSP_NET_INET_MSG_EOR:
		return MSG_EOR;
#endif
	case PSP_NET_INET_MSG_TRUNC:
		return MSG_TRUNC;
	case PSP_NET_INET_MSG_CTRUNC:
		return MSG_CTRUNC;
	case PSP_NET_INET_MSG_WAITALL:
		return MSG_WAITALL;
#if defined(MSG_DONTWAIT)
	case PSP_NET_INET_MSG_DONTWAIT:
		return MSG_DONTWAIT;
#endif
#if defined(MSG_BCAST)
	case PSP_NET_INET_MSG_BCAST:
		return MSG_BCAST;
#endif
#if defined(MSG_MCAST)
	case PSP_NET_INET_MSG_MCAST:
		return MSG_MCAST;
#endif
	}
	return hleLogError(SCENET, flag, "Unknown MSG flag");
}

int convertMsgFlagHost2PSP(int flag) {
	switch (flag) {
	case MSG_OOB:
		return PSP_NET_INET_MSG_OOB;
	case MSG_PEEK:
		return PSP_NET_INET_MSG_PEEK;
	case MSG_DONTROUTE:
		return PSP_NET_INET_MSG_DONTROUTE;
#if defined(MSG_EOR)
	case MSG_EOR:
		return PSP_NET_INET_MSG_EOR;
#endif
	case MSG_TRUNC:
		return PSP_NET_INET_MSG_TRUNC;
	case MSG_CTRUNC:
		return PSP_NET_INET_MSG_CTRUNC;
	case MSG_WAITALL:
		return PSP_NET_INET_MSG_WAITALL;
#if defined(MSG_DONTWAIT)
	case MSG_DONTWAIT:
		return PSP_NET_INET_MSG_DONTWAIT;
#endif
#if defined(MSG_BCAST)
	case MSG_BCAST:
		return PSP_NET_INET_MSG_BCAST;
#endif
#if defined(MSG_MCAST)
	case MSG_MCAST:
		return PSP_NET_INET_MSG_MCAST;
#endif
	}
	return hleLogError(SCENET, flag, "Unknown MSG flag");
}

int convertMSGFlagsPSP2Host(int flags) {
	// Only takes compatible one
	int flgs = 0;
	if (flags & PSP_NET_INET_MSG_OOB) {
		flgs |= MSG_OOB;
	}
	if (flags & PSP_NET_INET_MSG_PEEK) {
		flgs |= MSG_PEEK;
	}
	if (flags & PSP_NET_INET_MSG_DONTROUTE) {
		flgs |= MSG_DONTROUTE;
	}
#if defined(MSG_EOR)
	if (flags & PSP_NET_INET_MSG_EOR) {
		flgs |= MSG_EOR;
	}
#endif
	if (flags & PSP_NET_INET_MSG_TRUNC) {
		flgs |= MSG_TRUNC;
	}
	if (flags & PSP_NET_INET_MSG_CTRUNC) {
		flgs |= MSG_CTRUNC;
	}
	if (flags & PSP_NET_INET_MSG_WAITALL) {
		flgs |= MSG_WAITALL;
	}
#if defined(MSG_DONTWAIT)
	if (flags & PSP_NET_INET_MSG_DONTWAIT) {
		flgs |= MSG_DONTWAIT;
	}
#endif
#if defined(MSG_BCAST)
	if (flags & PSP_NET_INET_MSG_BCAST) {
		flgs |= MSG_BCAST;
	}
#endif
#if defined(MSG_MCAST)
	if (flags & PSP_NET_INET_MSG_MCAST) {
		flgs |= MSG_MCAST;
	}
#endif

	return flgs;
}

int convertMSGFlagsHost2PSP(int flags) {
	// Only takes compatible one
	int flgs = 0;
	if (flags & MSG_OOB) {
		flgs |= PSP_NET_INET_MSG_OOB;
	}
	if (flags & MSG_PEEK) {
		flgs |= PSP_NET_INET_MSG_PEEK;
	}
	if (flags & MSG_DONTROUTE) {
		flgs |= PSP_NET_INET_MSG_DONTROUTE;
	}
#if defined(MSG_EOR)
	if (flags & MSG_EOR) {
		flgs |= PSP_NET_INET_MSG_EOR;
	}
#endif
	if (flags & MSG_TRUNC) {
		flgs |= PSP_NET_INET_MSG_TRUNC;
	}
	if (flags & MSG_CTRUNC) {
		flgs |= PSP_NET_INET_MSG_CTRUNC;
	}
	if (flags & MSG_WAITALL) {
		flgs |= PSP_NET_INET_MSG_WAITALL;
	}
#if defined(MSG_DONTWAIT)
	if (flags & MSG_DONTWAIT) {
		flgs |= PSP_NET_INET_MSG_DONTWAIT;
	}
#endif
#if defined(MSG_BCAST)
	if (flags & MSG_BCAST) {
		flgs |= PSP_NET_INET_MSG_BCAST;
	}
#endif
#if defined(MSG_MCAST)
	if (flags & MSG_MCAST) {
		flgs |= PSP_NET_INET_MSG_MCAST;
	}
#endif

	return flgs;
}

int convertSocketDomainPSP2Host(int domain) {
	switch (domain) {
	case PSP_NET_INET_AF_UNSPEC:
		return AF_UNSPEC;
	case PSP_NET_INET_AF_LOCAL:
		return AF_UNIX;
	case PSP_NET_INET_AF_INET:
		return AF_INET;
	}
	return hleLogError(SCENET, domain, "Unknown Socket Domain");
}

int convertSocketDomainHost2PSP(int domain) {
	switch (domain) {
	case AF_UNSPEC:
		return PSP_NET_INET_AF_UNSPEC;
	case AF_UNIX:
		return PSP_NET_INET_AF_LOCAL;
	case AF_INET:
		return PSP_NET_INET_AF_INET;
	}
	return hleLogError(SCENET, domain, "Unknown Socket Domain");
}

std::string inetSocketDomain2str(int domain) {
	switch (domain) {
	case PSP_NET_INET_AF_UNSPEC:
		return "AF_UNSPEC";
	case PSP_NET_INET_AF_UNIX:
		return "AF_UNIX";
	case PSP_NET_INET_AF_INET:
		return "AF_INET";
	}
	return "AF_" + StringFromFormat("%08x", domain);
}

int convertSocketTypePSP2Host(int type) {
	// FIXME: Masked with 0x0F since there might be additional flags mixed in socket type that need to be converted too
	switch (type & PSP_NET_INET_SOCK_TYPE_MASK) {
	case PSP_NET_INET_SOCK_STREAM:
		return SOCK_STREAM;
	case PSP_NET_INET_SOCK_DGRAM:
		return SOCK_DGRAM;
	case PSP_NET_INET_SOCK_RAW:
		// FIXME: SOCK_RAW have some restrictions on newer Windows?
		return SOCK_RAW;
	case PSP_NET_INET_SOCK_RDM:
		return SOCK_RDM;
	case PSP_NET_INET_SOCK_SEQPACKET:
		return SOCK_SEQPACKET;
	case PSP_NET_INET_SOCK_CONN_DGRAM:	// PSP_NET_INET_SOCK_DCCP?
		return SOCK_DGRAM;				// SOCK_RAW?
	case PSP_NET_INET_SOCK_PACKET:
		return SOCK_STREAM;				// SOCK_RAW?
	}

	return hleLogError(SCENET, type, "Unknown Socket Type") & PSP_NET_INET_SOCK_TYPE_MASK;
}

int convertSocketTypeHost2PSP(int type) {
	// FIXME: Masked with 0x0F since there might be additional flags mixed in socket type that need to be converted too
	switch (type & PSP_NET_INET_SOCK_TYPE_MASK) {
	case SOCK_STREAM:
		return PSP_NET_INET_SOCK_STREAM;
	case SOCK_DGRAM:
		return PSP_NET_INET_SOCK_DGRAM;
	case SOCK_RAW:
		return PSP_NET_INET_SOCK_RAW;
	case SOCK_RDM:
		return PSP_NET_INET_SOCK_RDM;
	case SOCK_SEQPACKET:
		return PSP_NET_INET_SOCK_SEQPACKET;
#if defined(CONN_DGRAM)
	case CONN_DGRAM: // SOCK_DCCP
		return PSP_NET_INET_SOCK_CONN_DGRAM; // PSP_NET_INET_SOCK_DCCP
#endif
#if defined(SOCK_PACKET)
	case SOCK_PACKET:
		return PSP_NET_INET_SOCK_PACKET;
#endif
	}

	return hleLogError(SCENET, type, "Unknown Socket Type") & PSP_NET_INET_SOCK_TYPE_MASK;
}

std::string inetSocketType2str(int type) {
	switch (type & PSP_NET_INET_SOCK_TYPE_MASK) {
	case PSP_NET_INET_SOCK_STREAM:
		return "SOCK_STREAM";
	case PSP_NET_INET_SOCK_DGRAM:
		return "SOCK_DGRAM";
	case PSP_NET_INET_SOCK_RAW:
		return "SOCK_RAW";
	case PSP_NET_INET_SOCK_RDM:
		return "SOCK_RDM";
	case PSP_NET_INET_SOCK_SEQPACKET:
		return "SOCK_SEQPACKET";
	case PSP_NET_INET_SOCK_DCCP:
		return "SOCK_DCCP/SOCK_CONN_DGRAM?";
	case PSP_NET_INET_SOCK_PACKET:
		return "SOCK_PACKET?";
	}
	return "SOCK_" + StringFromFormat("%08x", type);
}

int convertSocketProtoPSP2Host(int protocol) {
	switch (protocol) {
	case PSP_NET_INET_IPPROTO_UNSPEC:
		return PSP_NET_INET_IPPROTO_UNSPEC; // 0 only valid if there is only 1 protocol available for a particular domain/family and type?
	case PSP_NET_INET_IPPROTO_ICMP:
		return IPPROTO_ICMP;
	case PSP_NET_INET_IPPROTO_IGMP:
		return IPPROTO_IGMP;
	case PSP_NET_INET_IPPROTO_TCP:
		return IPPROTO_TCP;
	case PSP_NET_INET_IPPROTO_EGP:
		return IPPROTO_EGP;
	case PSP_NET_INET_IPPROTO_PUP:
		return IPPROTO_PUP;
	case PSP_NET_INET_IPPROTO_UDP:
		return IPPROTO_UDP;
	case PSP_NET_INET_IPPROTO_IDP:
		return IPPROTO_IDP;
	case PSP_NET_INET_IPPROTO_RAW:
		return IPPROTO_RAW;
	}
	return hleLogError(SCENET, protocol, "Unknown Socket Protocol");
}

int convertSocketProtoHost2PSP(int protocol) {
	switch (protocol) {
	case PSP_NET_INET_IPPROTO_UNSPEC:
		return PSP_NET_INET_IPPROTO_UNSPEC; // 0 only valid if there is only 1 protocol available for a particular domain/family and type?
	case IPPROTO_ICMP:
		return PSP_NET_INET_IPPROTO_ICMP;
	case IPPROTO_IGMP:
		return PSP_NET_INET_IPPROTO_IGMP;
	case IPPROTO_TCP:
		return PSP_NET_INET_IPPROTO_TCP;
	case IPPROTO_EGP:
		return PSP_NET_INET_IPPROTO_EGP;
	case IPPROTO_PUP:
		return PSP_NET_INET_IPPROTO_PUP;
	case IPPROTO_UDP:
		return PSP_NET_INET_IPPROTO_UDP;
	case IPPROTO_IDP:
		return PSP_NET_INET_IPPROTO_IDP;
	case IPPROTO_RAW:
		return PSP_NET_INET_IPPROTO_RAW;
	}
	return hleLogError(SCENET, protocol, "Unknown Socket Protocol");
}

std::string inetSocketProto2str(int protocol) {
	switch (protocol) {
	case PSP_NET_INET_IPPROTO_UNSPEC:
		return "IPPROTO_UNSPEC (DEFAULT?)"; // defaulted to IPPROTO_TCP for SOCK_STREAM and IPPROTO_UDP for SOCK_DGRAM
	case PSP_NET_INET_IPPROTO_ICMP:
		return "IPPROTO_ICMP";
	case PSP_NET_INET_IPPROTO_IGMP:
		return "IPPROTO_IGMP";
	case PSP_NET_INET_IPPROTO_TCP:
		return "IPPROTO_TCP";
	case PSP_NET_INET_IPPROTO_EGP:
		return "IPPROTO_EGP";
	case PSP_NET_INET_IPPROTO_PUP:
		return "IPPROTO_PUP";
	case PSP_NET_INET_IPPROTO_UDP:
		return "IPPROTO_UDP";
	case PSP_NET_INET_IPPROTO_IDP:
		return "IPPROTO_IDP";
	case PSP_NET_INET_IPPROTO_RAW:
		return "IPPROTO_RAW";
	}
	return "IPPROTO_" + StringFromFormat("%08x", protocol);
}

int convertCMsgTypePSP2Host(int type, int level) {
	if (level == PSP_NET_INET_IPPROTO_IP) {
		switch (type) {
#if defined(IP_RECVDSTADDR)
		case PSP_NET_INET_IP_RECVDSTADDR:
			return IP_RECVDSTADDR;
#endif
#if defined(IP_RECVIF)
		case PSP_NET_INET_IP_RECVIF:
			return IP_RECVIF;
#endif
		}
	}
	else if (level == PSP_NET_INET_SOL_SOCKET) {
#if defined(SCM_RIGHTS)
		if (type == PSP_NET_INET_SCM_RIGHTS)
			return SCM_RIGHTS;
#endif
#if defined(SCM_CREDS)
		if (type == PSP_NET_INET_SCM_CREDS)
			return SCM_CREDS;
#endif
#if defined(SCM_TIMESTAMP)
		if (type == PSP_NET_INET_SCM_TIMESTAMP)
			return SCM_TIMESTAMP;
#endif
	}
	return hleLogError(SCENET, type, "Unknown CMSG_TYPE (Level = %08x)", level);
}

int convertCMsgTypeHost2PSP(int type, int level) {
	if (level == IPPROTO_IP) {
		switch (type) {
#if defined(IP_RECVDSTADDR)
		case IP_RECVDSTADDR:
			return PSP_NET_INET_IP_RECVDSTADDR;
#endif
#if defined(IP_RECVIF)
		case IP_RECVIF:
			return PSP_NET_INET_IP_RECVIF;
#endif
		}
	}
	else if (level == SOL_SOCKET) {
#if defined(SCM_RIGHTS)
		if (type == SCM_RIGHTS)
			return PSP_NET_INET_SCM_RIGHTS;
#endif
#if defined(SCM_CREDS)
		if (type == SCM_CREDS)
			return PSP_NET_INET_SCM_CREDS;
#endif
#if defined(SCM_TIMESTAMP)
		if (type == SCM_TIMESTAMP)
			return PSP_NET_INET_SCM_TIMESTAMP;
#endif
	}
	return hleLogError(SCENET, type, "Unknown CMSG_TYPE (Level = %08x)", level);
}

int convertSockoptLevelPSP2Host(int level) {
	switch (level) {
	case PSP_NET_INET_IPPROTO_IP:
		return IPPROTO_IP;
	case PSP_NET_INET_IPPROTO_TCP:
		return IPPROTO_TCP;
	case PSP_NET_INET_IPPROTO_UDP:
		return IPPROTO_UDP;
	case PSP_NET_INET_SOL_SOCKET:
		return SOL_SOCKET;
	}
	return hleLogError(SCENET, level, "Unknown SockOpt Level");
}

int convertSockoptLevelHost2PSP(int level) {
	switch (level) {
	case IPPROTO_IP:
		return PSP_NET_INET_IPPROTO_IP;
	case IPPROTO_TCP:
		return PSP_NET_INET_IPPROTO_TCP;
	case IPPROTO_UDP:
		return PSP_NET_INET_IPPROTO_UDP;
	case SOL_SOCKET:
		return PSP_NET_INET_SOL_SOCKET;
	}
	return hleLogError(SCENET, level, "Unknown SockOpt Level");
}

std::string inetSockoptLevel2str(int level) {
	switch (level) {
	case PSP_NET_INET_IPPROTO_IP:
		return "IPPROTO_IP";
	case PSP_NET_INET_IPPROTO_TCP:
		return "IPPROTO_TCP";
	case PSP_NET_INET_IPPROTO_UDP:
		return "IPPROTO_UDP";
	case PSP_NET_INET_SOL_SOCKET:
		return "SOL_SOCKET";
	}
	return "SOL_" + StringFromFormat("%08x", level);
}

int convertSockoptNamePSP2Host(int optname, int level) {
	if (level == PSP_NET_INET_IPPROTO_TCP) {
		switch (optname) {
		case PSP_NET_INET_TCP_NODELAY:
			return TCP_NODELAY;
		case PSP_NET_INET_TCP_MAXSEG:
			return TCP_MAXSEG;
		}
	}
	else if (level == PSP_NET_INET_IPPROTO_IP) {
		switch (optname) {
		case PSP_NET_INET_IP_OPTIONS:
			return IP_OPTIONS;
		case PSP_NET_INET_IP_HDRINCL:
			return IP_HDRINCL;
		case PSP_NET_INET_IP_TOS:
			return IP_TOS;
		case PSP_NET_INET_IP_TTL:
			return IP_TTL;
#if defined(IP_RECVOPTS)
		case PSP_NET_INET_IP_RECVOPTS:
			return IP_RECVOPTS;
#endif
#if defined(IP_RECVRETOPTS)
		case PSP_NET_INET_IP_RECVRETOPTS:
			return IP_RECVRETOPTS;
#endif
#if defined(IP_RECVDSTADDR)
		case PSP_NET_INET_IP_RECVDSTADDR:
			return IP_RECVDSTADDR;
#endif
#if defined(IP_RETOPTS)
		case PSP_NET_INET_IP_RETOPTS:
			return IP_RETOPTS;
#endif
		case PSP_NET_INET_IP_MULTICAST_IF:
			return IP_MULTICAST_IF;
		case PSP_NET_INET_IP_MULTICAST_TTL:
			return IP_MULTICAST_TTL;
		case PSP_NET_INET_IP_MULTICAST_LOOP:
			return IP_MULTICAST_LOOP;
		case PSP_NET_INET_IP_ADD_MEMBERSHIP:
			return IP_ADD_MEMBERSHIP;
		case PSP_NET_INET_IP_DROP_MEMBERSHIP:
			return IP_DROP_MEMBERSHIP;
#if defined(IP_PORTRANGE)
		case PSP_NET_INET_IP_PORTRANGE:
			return IP_PORTRANGE;
#endif
#if defined(IP_RECVIF)
		case PSP_NET_INET_IP_RECVIF:
			return IP_RECVIF;
#endif
#if defined(IP_ERRORMTU)
		case PSP_NET_INET_IP_ERRORMTU:
			return IP_ERRORMTU;
#endif
#if defined(IP_IPSEC_POLICY)
		case PSP_NET_INET_IP_IPSEC_POLICY:
			return IP_IPSEC_POLICY;
#endif
		}
	}
	else if (level == PSP_NET_INET_SOL_SOCKET) {
		switch (optname) {
		case PSP_NET_INET_SO_DEBUG:
			return SO_DEBUG;
		case PSP_NET_INET_SO_ACCEPTCONN:
			return SO_ACCEPTCONN;
		case PSP_NET_INET_SO_REUSEADDR:
			return SO_REUSEADDR;
		case PSP_NET_INET_SO_KEEPALIVE:
			return SO_KEEPALIVE;
		case PSP_NET_INET_SO_DONTROUTE:
			return SO_DONTROUTE;
		case PSP_NET_INET_SO_BROADCAST:
			return SO_BROADCAST;
#if defined(SO_USELOOPBACK)
		case PSP_NET_INET_SO_USELOOPBACK:
			return SO_USELOOPBACK;
#endif
		case PSP_NET_INET_SO_LINGER:
			return SO_LINGER;
		case PSP_NET_INET_SO_OOBINLINE:
			return SO_OOBINLINE;
#if defined(SO_REUSEPORT)
		case PSP_NET_INET_SO_REUSEPORT:
			return SO_REUSEPORT;
#endif
#if defined(SO_TIMESTAMP)
		case PSP_NET_INET_SO_TIMESTAMP:
			return SO_TIMESTAMP;
#endif
#if defined(SO_ONESBCAST)
		case PSP_NET_INET_SO_ONESBCAST:
			return SO_ONESBCAST;
#endif
		case PSP_NET_INET_SO_SNDBUF:
			return SO_SNDBUF;
		case PSP_NET_INET_SO_RCVBUF:
			return SO_RCVBUF;
		case PSP_NET_INET_SO_SNDLOWAT:
			return SO_SNDLOWAT;
		case PSP_NET_INET_SO_RCVLOWAT:
			return SO_RCVLOWAT;
		case PSP_NET_INET_SO_SNDTIMEO:
			return SO_SNDTIMEO;
		case PSP_NET_INET_SO_RCVTIMEO:
			return SO_RCVTIMEO;
		case PSP_NET_INET_SO_ERROR:
			return SO_ERROR;
		case PSP_NET_INET_SO_TYPE:
			return SO_TYPE;
#if defined(SO_NBIO)
		case PSP_NET_INET_SO_NBIO:
			return SO_NBIO;
#endif
#if defined(SO_BIO)
		case PSP_NET_INET_SO_BIO:
			return SO_BIO;
#endif
		}
	}
	return hleLogError(SCENET, optname, "Unknown PSP's SockOpt Name (Level = %08x)", level);
}

int convertSockoptNameHost2PSP(int optname, int level) {
	if (level == IPPROTO_TCP) {
		switch (optname) {
		case TCP_NODELAY:
			return PSP_NET_INET_TCP_NODELAY;
		case TCP_MAXSEG:
			return PSP_NET_INET_TCP_MAXSEG;
		}
	}
	else if (level == IPPROTO_IP) {
		switch (optname) {
		case IP_OPTIONS:
			return PSP_NET_INET_IP_OPTIONS;
		case IP_HDRINCL:
			return PSP_NET_INET_IP_HDRINCL;
		case IP_TOS:
			return PSP_NET_INET_IP_TOS;
		case IP_TTL:
			return PSP_NET_INET_IP_TTL;
#if defined(IP_RECVOPTS)
		case IP_RECVOPTS:
			return PSP_NET_INET_IP_RECVOPTS;
#endif
#if defined(IP_RECVRETOPTS) && (IP_RECVRETOPTS != IP_RETOPTS)
		case IP_RECVRETOPTS:
			return PSP_NET_INET_IP_RECVRETOPTS;
#endif
#if defined(IP_RECVDSTADDR)
		case IP_RECVDSTADDR:
			return PSP_NET_INET_IP_RECVDSTADDR;
#endif
#if defined(IP_RETOPTS)
		case IP_RETOPTS:
			return PSP_NET_INET_IP_RETOPTS;
#endif
		case IP_MULTICAST_IF:
			return PSP_NET_INET_IP_MULTICAST_IF;
		case IP_MULTICAST_TTL:
			return PSP_NET_INET_IP_MULTICAST_TTL;
		case IP_MULTICAST_LOOP:
			return PSP_NET_INET_IP_MULTICAST_LOOP;
		case IP_ADD_MEMBERSHIP:
			return PSP_NET_INET_IP_ADD_MEMBERSHIP;
		case IP_DROP_MEMBERSHIP:
			return PSP_NET_INET_IP_DROP_MEMBERSHIP;
#if defined(IP_PORTRANGE)
		case IP_PORTRANGE:
			return PSP_NET_INET_IP_PORTRANGE;
#endif
#if defined(IP_RECVIF)
		case PSP_NET_INET_IP_RECVIF:
			return IP_RECVIF;
#endif
#if defined(IP_ERRORMTU)
		case IP_ERRORMTU:
			return PSP_NET_INET_IP_ERRORMTU;
#endif
#if defined(IP_IPSEC_POLICY)
		case IP_IPSEC_POLICY:
			return PSP_NET_INET_IP_IPSEC_POLICY;
#endif
		}
	}
	else if (level == SOL_SOCKET) {
		switch (optname) {
		case SO_DEBUG:
			return PSP_NET_INET_SO_DEBUG;
		case SO_ACCEPTCONN:
			return PSP_NET_INET_SO_ACCEPTCONN;
		case SO_REUSEADDR:
			return PSP_NET_INET_SO_REUSEADDR;
		case SO_KEEPALIVE:
			return PSP_NET_INET_SO_KEEPALIVE;
		case SO_DONTROUTE:
			return PSP_NET_INET_SO_DONTROUTE;
		case SO_BROADCAST:
			return PSP_NET_INET_SO_BROADCAST;
#if defined(SO_USELOOPBACK)
		case SO_USELOOPBACK:
			return PSP_NET_INET_SO_USELOOPBACK;
#endif
		case SO_LINGER:
			return PSP_NET_INET_SO_LINGER;
		case SO_OOBINLINE:
			return PSP_NET_INET_SO_OOBINLINE;
#if defined(SO_REUSEPORT)
		case SO_REUSEPORT:
			return PSP_NET_INET_SO_REUSEPORT;
#endif
#if defined(SO_TIMESTAMP)
		case SO_TIMESTAMP:
			return PSP_NET_INET_SO_TIMESTAMP;
#endif
#if defined(SO_ONESBCAST)
		case SO_ONESBCAST:
			return PSP_NET_INET_SO_ONESBCAST;
#endif
		case SO_SNDBUF:
			return PSP_NET_INET_SO_SNDBUF;
		case SO_RCVBUF:
			return PSP_NET_INET_SO_RCVBUF;
		case SO_SNDLOWAT:
			return PSP_NET_INET_SO_SNDLOWAT;
		case SO_RCVLOWAT:
			return PSP_NET_INET_SO_RCVLOWAT;
		case SO_SNDTIMEO:
			return PSP_NET_INET_SO_SNDTIMEO;
		case SO_RCVTIMEO:
			return PSP_NET_INET_SO_RCVTIMEO;
		case SO_ERROR:
			return PSP_NET_INET_SO_ERROR;
		case SO_TYPE:
			return PSP_NET_INET_SO_TYPE;
#if defined(SO_NBIO)
		case SO_NBIO:
			return PSP_NET_INET_SO_NBIO;
#endif
#if defined(SO_BIO)
		case SO_BIO:
			return PSP_NET_INET_SO_BIO;
#endif
		}
	}
	return hleLogError(SCENET, optname, "Unknown Host's SockOpt Name (Level = %08x)", level);
}

std::string inetSockoptName2str(int optname, int level) {
	if (level == PSP_NET_INET_IPPROTO_TCP) {
		switch (optname) {
		case PSP_NET_INET_TCP_NODELAY:
			return "TCP_NODELAY";
		case PSP_NET_INET_TCP_MAXSEG:
			return "TCP_MAXSEG";
		}
	}
	else if (level == PSP_NET_INET_IPPROTO_IP) {
		switch (optname) {
		case PSP_NET_INET_IP_OPTIONS:
			return "IP_OPTIONS";
		case PSP_NET_INET_IP_HDRINCL:
			return "IP_HDRINCL";
		case PSP_NET_INET_IP_TOS:
			return "IP_TOS";
		case PSP_NET_INET_IP_TTL:
			return "IP_TTL";
		case PSP_NET_INET_IP_RECVOPTS:
			return "IP_RECVOPTS";
		case PSP_NET_INET_IP_RECVRETOPTS:
			return "IP_RECVRETOPTS";
		case PSP_NET_INET_IP_RECVDSTADDR:
			return "IP_RECVDSTADDR";
		case PSP_NET_INET_IP_RETOPTS:
			return "IP_RETOPTS";
		case PSP_NET_INET_IP_MULTICAST_IF:
			return "IP_MULTICAST_IF";
		case PSP_NET_INET_IP_MULTICAST_TTL:
			return "IP_MULTICAST_TTL";
		case PSP_NET_INET_IP_MULTICAST_LOOP:
			return "IP_MULTICAST_LOOP";
		case PSP_NET_INET_IP_ADD_MEMBERSHIP:
			return "IP_ADD_MEMBERSHIP";
		case PSP_NET_INET_IP_DROP_MEMBERSHIP:
			return "IP_DROP_MEMBERSHIP";
		case PSP_NET_INET_IP_PORTRANGE:
			return "IP_PORTRANGE";
		case PSP_NET_INET_IP_RECVIF:
			return "IP_RECVIF";
		case PSP_NET_INET_IP_ERRORMTU:
			return "IP_ERRORMTU";
		case PSP_NET_INET_IP_IPSEC_POLICY:
			return "IP_IPSEC_POLICY";
		}
	}
	else if (level == PSP_NET_INET_SOL_SOCKET) {
		switch (optname) {
		case PSP_NET_INET_SO_DEBUG:
			return "SO_DEBUG";
		case PSP_NET_INET_SO_ACCEPTCONN:
			return "SO_ACCEPTCONN";
		case PSP_NET_INET_SO_REUSEADDR:
			return "SO_REUSEADDR";
		case PSP_NET_INET_SO_KEEPALIVE:
			return "SO_KEEPALIVE";
		case PSP_NET_INET_SO_DONTROUTE:
			return "SO_DONTROUTE";
		case PSP_NET_INET_SO_BROADCAST:
			return "SO_BROADCAST";
		case PSP_NET_INET_SO_USELOOPBACK:
			return "SO_USELOOPBACK";
		case PSP_NET_INET_SO_LINGER:
			return "SO_LINGER";
		case PSP_NET_INET_SO_OOBINLINE:
			return "SO_OOBINLINE";
		case PSP_NET_INET_SO_REUSEPORT:
			return "SO_REUSEPORT";
		case PSP_NET_INET_SO_TIMESTAMP:
			return "SO_TIMESTAMP";
		case PSP_NET_INET_SO_ONESBCAST:
			return "SO_ONESBCAST";
		case PSP_NET_INET_SO_SNDBUF:
			return "SO_SNDBUF";
		case PSP_NET_INET_SO_RCVBUF:
			return "SO_RCVBUF";
		case PSP_NET_INET_SO_SNDLOWAT:
			return "SO_SNDLOWAT";
		case PSP_NET_INET_SO_RCVLOWAT:
			return "SO_RCVLOWAT";
		case PSP_NET_INET_SO_SNDTIMEO:
			return "SO_SNDTIMEO";
		case PSP_NET_INET_SO_RCVTIMEO:
			return "SO_RCVTIMEO";
		case PSP_NET_INET_SO_ERROR:
			return "SO_ERROR";
		case PSP_NET_INET_SO_TYPE:
			return "SO_TYPE";
		case PSP_NET_INET_SO_NBIO:
			return "SO_NBIO"; // SO_NONBLOCK
		case PSP_NET_INET_SO_BIO:
			return "SO_BIO";
		}
	}
	return "SO_" + StringFromFormat("%08x (Level = %08x)", optname, level);
}

int convertInetErrnoHost2PSP(int error) {
	switch (error) {
	case EINTR:
		return ERROR_INET_EINTR;
	case EBADF:
		return ERROR_INET_EBADF;
	case EACCES:
		return ERROR_INET_EACCES;
	case EFAULT:
		return ERROR_INET_EFAULT;
	case EINVAL:
		return ERROR_INET_EINVAL;
	case ENOSPC:
		return ERROR_INET_ENOSPC;
	case EPIPE:
		return ERROR_INET_EPIPE;
	case ENOMSG:
		return ERROR_INET_ENOMSG;
	case ENOLINK:
		return ERROR_INET_ENOLINK;
	case EPROTO:
		return ERROR_INET_EPROTO;
	case EBADMSG:
		return ERROR_INET_EBADMSG;
	case EOPNOTSUPP:
		return ERROR_INET_EOPNOTSUPP;
	case EPFNOSUPPORT:
		return ERROR_INET_EPFNOSUPPORT;
	case ECONNRESET:
		return ERROR_INET_ECONNRESET;
	case ENOBUFS:
		return ERROR_INET_ENOBUFS;
	case EAFNOSUPPORT:
		return ERROR_INET_EAFNOSUPPORT;
	case EPROTOTYPE:
		return ERROR_INET_EPROTOTYPE;
	case ENOTSOCK:
		return ERROR_INET_ENOTSOCK;
	case ENOPROTOOPT:
		return ERROR_INET_ENOPROTOOPT;
	case ESHUTDOWN:
		return ERROR_INET_ESHUTDOWN;
	case ECONNREFUSED:
		return ERROR_INET_ECONNREFUSED;
	case EADDRINUSE:
		return ERROR_INET_EADDRINUSE;
	case ECONNABORTED:
		return ERROR_INET_ECONNABORTED;
	case ENETUNREACH:
		return ERROR_INET_ENETUNREACH;
	case ENETDOWN:
		return ERROR_INET_ENETDOWN;
	case ETIMEDOUT:
		return ERROR_INET_ETIMEDOUT;
	case EHOSTDOWN:
		return ERROR_INET_EHOSTDOWN;
	case EHOSTUNREACH:
		return ERROR_INET_EHOSTUNREACH;
	case EALREADY:
		return ERROR_INET_EALREADY;
	case EMSGSIZE:
		return ERROR_INET_EMSGSIZE;
	case EPROTONOSUPPORT:
		return ERROR_INET_EPROTONOSUPPORT;
	case ESOCKTNOSUPPORT:
		return ERROR_INET_ESOCKTNOSUPPORT;
	case EADDRNOTAVAIL:
		return ERROR_INET_EADDRNOTAVAIL;
	case ENETRESET:
		return ERROR_INET_ENETRESET;
	case EISCONN:
		return ERROR_INET_EISCONN;
	case ENOTCONN:
		return ERROR_INET_ENOTCONN;
	case EAGAIN:
		return ERROR_INET_EAGAIN;
#if !defined(_WIN32)
	case EINPROGRESS:
		return ERROR_INET_EINPROGRESS;
#endif
	}
	if (error != 0)
		return hleLogError(SCENET, error, "Unknown Error Number (%d)", error);
	return error;
}

// FIXME: Some of this might be wrong
int convertInetErrno2PSPError(int error) {
	switch (error) {
	case ERROR_INET_EINTR:
		return SCE_KERNEL_ERROR_ERRNO_DEVICE_BUSY;
	case ERROR_INET_EACCES:
		return SCE_KERNEL_ERROR_ERRNO_READ_ONLY;
	case ERROR_INET_EFAULT:
		return SCE_KERNEL_ERROR_ERRNO_ADDR_OUT_OF_MAIN_MEM;
	case ERROR_INET_EINVAL:
		return SCE_KERNEL_ERROR_ERRNO_INVALID_ARGUMENT;
	case ERROR_INET_ENOSPC:
		return SCE_KERNEL_ERROR_ERRNO_NO_MEMORY;
	case ERROR_INET_EPIPE:
		return SCE_KERNEL_ERROR_ERRNO_FILE_NOT_FOUND;
	case ERROR_INET_ENOMSG:
		return SCE_KERNEL_ERROR_ERRNO_NO_MEDIA;
	case ERROR_INET_ENOLINK:
		return SCE_KERNEL_ERROR_ERRNO_DEVICE_NOT_FOUND;
	case ERROR_INET_EPROTO:
		return SCE_KERNEL_ERROR_ERRNO_FILE_PROTOCOL;
	case ERROR_INET_EBADMSG:
		return SCE_KERNEL_ERROR_ERRNO_INVALID_MEDIUM;
	case ERROR_INET_EOPNOTSUPP:
		return SCE_KERNEL_ERROR_ERRNO_FUNCTION_NOT_SUPPORTED;
	case ERROR_INET_EPFNOSUPPORT:
		return SCE_KERNEL_ERROR_ERRNO_FUNCTION_NOT_SUPPORTED;
	case ERROR_INET_ECONNRESET:
		return SCE_KERNEL_ERROR_ERRNO_CONNECTION_RESET;
	case ERROR_INET_ENOBUFS:
		return SCE_KERNEL_ERROR_ERRNO_NO_FREE_BUF_SPACE;
	case ERROR_INET_EAFNOSUPPORT:
		return SCE_KERNEL_ERROR_ERRNO_FUNCTION_NOT_SUPPORTED;
	case ERROR_INET_EPROTOTYPE:
		return SCE_KERNEL_ERROR_ERRNO_FILE_PROTOCOL;
	case ERROR_INET_ENOTSOCK:
		return SCE_KERNEL_ERROR_ERRNO_INVALID_FILE_DESCRIPTOR;
	case ERROR_INET_ENOPROTOOPT:
		return SCE_KERNEL_ERROR_ERRNO_FILE_PROTOCOL;
	case ERROR_INET_ESHUTDOWN:
		return SCE_KERNEL_ERROR_ERRNO_CLOSED;
	case ERROR_INET_ECONNREFUSED:
		return SCE_KERNEL_ERROR_ERRNO_FILE_ALREADY_EXISTS;
	case ERROR_INET_EADDRINUSE:
		return SCE_KERNEL_ERROR_ERRNO_FILE_ADDR_IN_USE;
	case ERROR_INET_ECONNABORTED:
		return SCE_KERNEL_ERROR_ERRNO_CONNECTION_ABORTED;
	case ERROR_INET_ENETUNREACH:
		return SCE_KERNEL_ERROR_ERRNO_DEVICE_NOT_FOUND;
	case ERROR_INET_ENETDOWN:
		return SCE_KERNEL_ERROR_ERRNO_CLOSED;
	case ERROR_INET_ETIMEDOUT:
		return SCE_KERNEL_ERROR_ERRNO_FILE_TIMEOUT;
	case ERROR_INET_EHOSTDOWN:
		return SCE_KERNEL_ERROR_ERRNO_CLOSED;
	case ERROR_INET_EHOSTUNREACH:
		return SCE_KERNEL_ERROR_ERRNO_DEVICE_NOT_FOUND;
	case ERROR_INET_EALREADY:
		return SCE_KERNEL_ERROR_ERRNO_ALREADY;
	case ERROR_INET_EMSGSIZE:
		return SCE_KERNEL_ERROR_ERRNO_FILE_IS_TOO_BIG;
	case ERROR_INET_EPROTONOSUPPORT:
		return SCE_KERNEL_ERROR_ERRNO_FUNCTION_NOT_SUPPORTED;
	case ERROR_INET_ESOCKTNOSUPPORT:
		return SCE_KERNEL_ERROR_ERRNO_FUNCTION_NOT_SUPPORTED;
	case ERROR_INET_EADDRNOTAVAIL:
		return SCE_KERNEL_ERROR_ERRNO_ADDRESS_NOT_AVAILABLE;
	case ERROR_INET_ENETRESET:
		return SCE_KERNEL_ERROR_ERRNO_CONNECTION_RESET;
	case ERROR_INET_EISCONN:
		return SCE_KERNEL_ERROR_ERRNO_ALREADY; // SCE_KERNEL_ERROR_ERRNO_IS_ALREADY_CONNECTED; // UNO only check for 0x80010077 and 0x80010078
	case ERROR_INET_ENOTCONN:
		return SCE_KERNEL_ERROR_ERRNO_NOT_CONNECTED;
	case ERROR_INET_EAGAIN:
		return SCE_KERNEL_ERROR_ERRNO_RESOURCE_UNAVAILABLE; // SCE_ERROR_ERRNO_EAGAIN;
#if !defined(_WIN32)
	case ERROR_INET_EINPROGRESS:
		return SCE_KERNEL_ERROR_ERRNO_IN_PROGRESS;
#endif
	}
	if (error != 0)
		return hleLogError(SCENET, error, "Unknown PSP Error Number (%d)", error);
	return error;
}

static int sceNetInetGetErrno() {
	if (inetLastErrno == 0) 
		inetLastErrno = errno;
	int error = convertInetErrnoHost2PSP(inetLastErrno);
	inetLastErrno = 0;
	return hleLogSuccessI(SCENET, error, " at %08x", currentMIPS->pc);
}

static int sceNetInetGetPspError() {
	if (inetLastErrno == 0)
		inetLastErrno = errno;
	int error = convertInetErrno2PSPError(convertInetErrnoHost2PSP(inetLastErrno));
	inetLastErrno = 0;
	return hleLogSuccessX(SCENET, error, " at %08x", currentMIPS->pc);
}

// Write static data since we don't actually manage any memory for sceNet* yet.
static int sceNetGetMallocStat(u32 statPtr) {
	VERBOSE_LOG(SCENET, "UNTESTED sceNetGetMallocStat(%x) at %08x", statPtr, currentMIPS->pc);
	auto stat = PSPPointer<SceNetMallocStat>::Create(statPtr);
	if (!stat.IsValid())
		return hleLogError(SCENET, 0, "invalid address");

	*stat = netMallocStat;
	stat.NotifyWrite("sceNetGetMallocStat");
	return 0;
}

static int sceNetInetInit() {
	ERROR_LOG(SCENET, "UNIMPL sceNetInetInit()");
	if (netInetInited) return ERROR_NET_INET_ALREADY_INITIALIZED;
	netInetInited = true;

	return 0;
}

int sceNetInetTerm() {
	ERROR_LOG(SCENET, "UNIMPL sceNetInetTerm()");
	netInetInited = false;
	// FIXME: Should we Shutdown/Close previously created sockets so we can reuse the ports on the next MP session?
	return 0;
}

void NetApctl_InitDefaultInfo() {
	memset(&netApctlInfo, 0, sizeof(netApctlInfo));
	// Set dummy/fake parameters, assuming this is the currently selected Network Configuration profile
	// FIXME: Some of these info supposed to be taken from netConfInfo
	int validConfId = std::max(1, netApctlInfoId); // Should be: sceUtilityGetNetParamLatestID(validConfId);
	truncate_cpy(netApctlInfo.name, sizeof(netApctlInfo.name), (defaultNetConfigName + std::to_string(validConfId)).c_str());
	truncate_cpy(netApctlInfo.ssid, sizeof(netApctlInfo.ssid), defaultNetSSID.c_str());
	// Default IP Address
	char ipstr[INET_ADDRSTRLEN] = "0.0.0.0"; // Driver 76 needs a dot formatted IP instead of a zeroed buffer
	truncate_cpy(netApctlInfo.ip, sizeof(netApctlInfo.ip), ipstr);
	truncate_cpy(netApctlInfo.gateway, sizeof(netApctlInfo.gateway), ipstr);
	truncate_cpy(netApctlInfo.primaryDns, sizeof(netApctlInfo.primaryDns), ipstr);
	truncate_cpy(netApctlInfo.secondaryDns, sizeof(netApctlInfo.secondaryDns), ipstr);
	truncate_cpy(netApctlInfo.subNetMask, sizeof(netApctlInfo.subNetMask), ipstr);
}

void NetApctl_InitInfo(int confId) {
	memset(&netApctlInfo, 0, sizeof(netApctlInfo));
	// Set dummy/fake values, some of these (ie. IP set to Auto) probably not suppose to have valid info before connected to an AP, right?
	// FIXME: Some of these info supposed to be taken from netConfInfo
	truncate_cpy(netApctlInfo.name, sizeof(netApctlInfo.name), (defaultNetConfigName + std::to_string(confId)).c_str());
	truncate_cpy(netApctlInfo.ssid, sizeof(netApctlInfo.ssid), defaultNetSSID.c_str());
	memcpy(netApctlInfo.bssid, "\1\1\2\2\3\3", sizeof(netApctlInfo.bssid)); // fake AP's mac address
	netApctlInfo.ssidLength = static_cast<unsigned int>(defaultNetSSID.length());
	netApctlInfo.strength = 99;
	netApctlInfo.channel = g_Config.iWlanAdhocChannel;
	if (netApctlInfo.channel == PSP_SYSTEMPARAM_ADHOC_CHANNEL_AUTOMATIC) netApctlInfo.channel = defaultWlanChannel;
	// Get Local IP Address
	sockaddr_in sockAddr;
	getLocalIp(&sockAddr); // This will be valid IP, we probably not suppose to have a valid IP before connected to any AP, right?
	char ipstr[INET_ADDRSTRLEN] = "127.0.0.1"; // Patapon 3 seems to try to get current IP using ApctlGetInfo() right after ApctlInit(), what kind of IP should we use as default before ApctlConnect()? it shouldn't be a valid IP, right?
	inet_ntop(AF_INET, &sockAddr.sin_addr, ipstr, sizeof(ipstr));
	truncate_cpy(netApctlInfo.ip, sizeof(netApctlInfo.ip), ipstr);
	// Change the last number to 1 to indicate a common dns server/internet gateway
	((u8*)&sockAddr.sin_addr.s_addr)[3] = 1;
	inet_ntop(AF_INET, &sockAddr.sin_addr, ipstr, sizeof(ipstr));
	truncate_cpy(netApctlInfo.gateway, sizeof(netApctlInfo.gateway), ipstr);
	// We should probably use public DNS Server instead of localhost IP since most people don't have DNS Server running on localhost (ie. Untold Legends The Warrior's Code is trying to lookup dns using the primary dns), but accessing public DNS Server from localhost may result to ENETUNREACH error if the gateway can't access the public server (ie. using SO_DONTROUTE)
	//if (strcmp(ipstr, "127.0.0.1") == 0)
		truncate_cpy(netApctlInfo.primaryDns, sizeof(netApctlInfo.primaryDns), g_Config.primaryDNSServer.c_str()); // Private Servers may need to use custom DNS Server
	//else
	//	truncate_cpy(netApctlInfo.primaryDns, sizeof(netApctlInfo.primaryDns), ipstr);
	truncate_cpy(netApctlInfo.secondaryDns, sizeof(netApctlInfo.secondaryDns), g_Config.secondaryDNSServer.c_str()); // Fireteam Bravo 2 seems to try to use secondary DNS too if it's not 0.0.0.0
	truncate_cpy(netApctlInfo.subNetMask, sizeof(netApctlInfo.subNetMask), "255.255.255.0");
}

static int sceNetApctlInit(int stackSize, int initPriority) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %i)", __FUNCTION__, stackSize, initPriority);
	if (netApctlInited)
		return ERROR_NET_APCTL_ALREADY_INITIALIZED;

	apctlEvents.clear();
	netApctlState = PSP_NET_APCTL_STATE_DISCONNECTED;

	// Set default value before connected to an AP
	NetApctl_InitDefaultInfo();

	// Create APctl fake-Thread
	netValidateLoopMemory();
	apctlThreadID = __KernelCreateThread("ApctlThread", __KernelGetCurThreadModuleId(), apctlThreadHackAddr, initPriority, stackSize, PSP_THREAD_ATTR_USER, 0, true);
	if (apctlThreadID > 0) {
		__KernelStartThread(apctlThreadID, 0, 0);
	}

	// Note: Borrowing AdhocServer for Grouping purpose
	u32 structsz = sizeof(SceNetAdhocctlAdhocId);
	if (apctlProdCodeAddr != 0) {
		userMemory.Free(apctlProdCodeAddr);
	}
	apctlProdCodeAddr = userMemory.Alloc(structsz, false, "ApctlAdhocId");
	SceNetAdhocctlAdhocId* prodCode = (SceNetAdhocctlAdhocId*)Memory::GetCharPointer(apctlProdCodeAddr);
	if (prodCode) {
		memset(prodCode, 0, structsz);
		// TODO: Use a 9-characters product id instead of disc id (ie. not null-terminated(VT_UTF8_SPE) and shouldn't be variable size?)
		std::string discID = g_paramSFO.GetDiscID();
		prodCode->type = 1; // VT_UTF8 since we're using DiscID instead of product id
		memcpy(prodCode->data, discID.c_str(), std::min(ADHOCCTL_ADHOCID_LEN, (int)discID.size()));
	}
	sceNetAdhocctlInit(stackSize, initPriority, apctlProdCodeAddr);

	netApctlInited = true;

	return 0;
}

int NetApctl_Term() {
	// Note: Since we're borrowing AdhocServer for Grouping purpose, we should cleanup too
	NetAdhocctl_Term();
	if (apctlProdCodeAddr != 0) {
		userMemory.Free(apctlProdCodeAddr);
		apctlProdCodeAddr = 0;
	}

	// Cleanup Apctl resources
	// Delete fake PSP Thread
	if (apctlThreadID != 0) {
		__KernelStopThread(apctlThreadID, SCE_KERNEL_ERROR_THREAD_TERMINATED, "ApctlThread stopped");
		__KernelDeleteThread(apctlThreadID, SCE_KERNEL_ERROR_THREAD_TERMINATED, "ApctlThread deleted");
		apctlThreadID = 0;
	}

	netApctlInited = false;
	netApctlState = PSP_NET_APCTL_STATE_DISCONNECTED;

	return 0;
}

int sceNetApctlTerm() {
	WARN_LOG(SCENET, "UNTESTED %s()", __FUNCTION__);
	int retval = NetApctl_Term();

	hleEatMicro(adhocDefaultDelay);
	return retval;
}

static int sceNetApctlGetInfo(int code, u32 pInfoAddr) {
	DEBUG_LOG(SCENET, "UNTESTED %s(%i, %08x) at %08x", __FUNCTION__, code, pInfoAddr, currentMIPS->pc);

	// FIXME: Driver 76 need to use sceNetApctlGetInfo without initializing/connecting Apctl, but they use Adhocctl instead, so may be sceNetApctlGetInfo also affected by Adhocctl? 
	//if (!netApctlInited)
	//	return hleLogError(SCENET, ERROR_NET_APCTL_NOT_INITIALIZED, "apctl not initialized?"); // FIXME: Official prx files seems to return 0x80410a0d when Apctl not initialized yet?

	//if (netApctlState != PSP_NET_APCTL_STATE_GOT_IP)
	//	return hleLogError(SCENET, ERROR_NET_APCTL_NOT_IN_BSS, "apctl not connected?"); // FIXME: Official prx files seems to return 0x80410a05 when Apctl not connected yet?

	switch (code) {
	case PSP_NET_APCTL_INFO_PROFILE_NAME:
		if (!Memory::IsValidRange(pInfoAddr, APCTL_PROFILENAME_MAXLEN))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::MemcpyUnchecked(pInfoAddr, netApctlInfo.name, APCTL_PROFILENAME_MAXLEN);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, APCTL_PROFILENAME_MAXLEN, "NetApctlGetInfo");
		DEBUG_LOG(SCENET, "ApctlInfo - ProfileName: %s", netApctlInfo.name);
		break;
	case PSP_NET_APCTL_INFO_BSSID:
		if (!Memory::IsValidRange(pInfoAddr, ETHER_ADDR_LEN))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::MemcpyUnchecked(pInfoAddr, netApctlInfo.bssid, ETHER_ADDR_LEN);
		DEBUG_LOG(SCENET, "ApctlInfo - BSSID: %s", mac2str((SceNetEtherAddr*)&netApctlInfo.bssid).c_str());
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, ETHER_ADDR_LEN, "NetApctlGetInfo");
		break;
	case PSP_NET_APCTL_INFO_SSID:
		if (!Memory::IsValidRange(pInfoAddr, APCTL_SSID_MAXLEN))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::MemcpyUnchecked(pInfoAddr, netApctlInfo.ssid, APCTL_SSID_MAXLEN);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, APCTL_SSID_MAXLEN, "NetApctlGetInfo");
		DEBUG_LOG(SCENET, "ApctlInfo - SSID: %s", netApctlInfo.ssid);
		break;
	case PSP_NET_APCTL_INFO_SSID_LENGTH:
		if (!Memory::IsValidRange(pInfoAddr, 4))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::WriteUnchecked_U32(netApctlInfo.ssidLength, pInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, 4, "NetApctlGetInfo");
		break;
	case PSP_NET_APCTL_INFO_SECURITY_TYPE:
		if (!Memory::IsValidRange(pInfoAddr, 4))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::WriteUnchecked_U32(netApctlInfo.securityType, pInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, 4, "NetApctlGetInfo");
		break;
	case PSP_NET_APCTL_INFO_STRENGTH:
		if (!Memory::IsValidRange(pInfoAddr, 1))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::WriteUnchecked_U8(netApctlInfo.strength, pInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, 1, "NetApctlGetInfo");
		break;
	case PSP_NET_APCTL_INFO_CHANNEL:
		if (!Memory::IsValidRange(pInfoAddr, 1))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::WriteUnchecked_U8(netApctlInfo.channel, pInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, 1, "NetApctlGetInfo");
		break;
	case PSP_NET_APCTL_INFO_POWER_SAVE:
		if (!Memory::IsValidRange(pInfoAddr, 1))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::WriteUnchecked_U8(netApctlInfo.powerSave, pInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, 1, "NetApctlGetInfo");
		break;
	case PSP_NET_APCTL_INFO_IP:
		if (!Memory::IsValidRange(pInfoAddr, APCTL_IPADDR_MAXLEN))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::MemcpyUnchecked(pInfoAddr, netApctlInfo.ip, APCTL_IPADDR_MAXLEN);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, APCTL_IPADDR_MAXLEN, "NetApctlGetInfo");
		DEBUG_LOG(SCENET, "ApctlInfo - IP: %s", netApctlInfo.ip);
		break;
	case PSP_NET_APCTL_INFO_SUBNETMASK:
		if (!Memory::IsValidRange(pInfoAddr, APCTL_IPADDR_MAXLEN))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::MemcpyUnchecked(pInfoAddr, netApctlInfo.subNetMask, APCTL_IPADDR_MAXLEN);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, APCTL_IPADDR_MAXLEN, "NetApctlGetInfo");
		DEBUG_LOG(SCENET, "ApctlInfo - SubNet Mask: %s", netApctlInfo.subNetMask);
		break;
	case PSP_NET_APCTL_INFO_GATEWAY:
		if (!Memory::IsValidRange(pInfoAddr, APCTL_IPADDR_MAXLEN))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::MemcpyUnchecked(pInfoAddr, netApctlInfo.gateway, APCTL_IPADDR_MAXLEN);
		DEBUG_LOG(SCENET, "ApctlInfo - Gateway IP: %s", netApctlInfo.gateway);
		break;
	case PSP_NET_APCTL_INFO_PRIMDNS:
		if (!Memory::IsValidRange(pInfoAddr, APCTL_IPADDR_MAXLEN))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::MemcpyUnchecked(pInfoAddr, netApctlInfo.primaryDns, APCTL_IPADDR_MAXLEN);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, APCTL_IPADDR_MAXLEN, "NetApctlGetInfo");
		DEBUG_LOG(SCENET, "ApctlInfo - Primary DNS: %s", netApctlInfo.primaryDns);
		break;
	case PSP_NET_APCTL_INFO_SECDNS:
		if (!Memory::IsValidRange(pInfoAddr, APCTL_IPADDR_MAXLEN))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::MemcpyUnchecked(pInfoAddr, netApctlInfo.secondaryDns, APCTL_IPADDR_MAXLEN);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, APCTL_IPADDR_MAXLEN, "NetApctlGetInfo");
		DEBUG_LOG(SCENET, "ApctlInfo - Secondary DNS: %s", netApctlInfo.secondaryDns);
		break;
	case PSP_NET_APCTL_INFO_USE_PROXY:
		if (!Memory::IsValidRange(pInfoAddr, 4))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::WriteUnchecked_U32(netApctlInfo.useProxy, pInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, 4, "NetApctlGetInfo");
		break;
	case PSP_NET_APCTL_INFO_PROXY_URL:
		if (!Memory::IsValidRange(pInfoAddr, APCTL_URL_MAXLEN))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::MemcpyUnchecked(pInfoAddr, netApctlInfo.proxyUrl, APCTL_URL_MAXLEN);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, APCTL_URL_MAXLEN, "NetApctlGetInfo");
		DEBUG_LOG(SCENET, "ApctlInfo - Proxy URL: %s", netApctlInfo.proxyUrl);
		break;
	case PSP_NET_APCTL_INFO_PROXY_PORT:
		if (!Memory::IsValidRange(pInfoAddr, 2))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::WriteUnchecked_U16(netApctlInfo.proxyPort, pInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, 2, "NetApctlGetInfo");
		break;
	case PSP_NET_APCTL_INFO_8021_EAP_TYPE:
		if (!Memory::IsValidRange(pInfoAddr, 4))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::WriteUnchecked_U32(netApctlInfo.eapType, pInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, 4, "NetApctlGetInfo");
		break;
	case PSP_NET_APCTL_INFO_START_BROWSER:
		if (!Memory::IsValidRange(pInfoAddr, 4))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::WriteUnchecked_U32(netApctlInfo.startBrowser, pInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, 4, "NetApctlGetInfo");
		break;
	case PSP_NET_APCTL_INFO_WIFISP:
		if (!Memory::IsValidRange(pInfoAddr, 4))
			return hleLogError(SCENET, -1, "apctl invalid arg");
		Memory::WriteUnchecked_U32(netApctlInfo.wifisp, pInfoAddr);
		NotifyMemInfo(MemBlockFlags::WRITE, pInfoAddr, 4, "NetApctlGetInfo");
		break;
	default:
		return hleLogError(SCENET, ERROR_NET_APCTL_INVALID_CODE, "apctl invalid code");
	}

	return hleLogSuccessI(SCENET, 0);
}

int NetApctl_AddHandler(u32 handlerPtr, u32 handlerArg) {
	bool foundHandler = false;
	u32 retval = 0;
	struct ApctlHandler handler;
	memset(&handler, 0, sizeof(handler));

	while (apctlHandlers.find(retval) != apctlHandlers.end())
		++retval;

	handler.entryPoint = handlerPtr;
	handler.argument = handlerArg;

	for (std::map<int, ApctlHandler>::iterator it = apctlHandlers.begin(); it != apctlHandlers.end(); it++) {
		if (it->second.entryPoint == handlerPtr) {
			foundHandler = true;
			break;
		}
	}

	if (!foundHandler && Memory::IsValidAddress(handlerPtr)) {
		if (apctlHandlers.size() >= MAX_APCTL_HANDLERS) {
			ERROR_LOG(SCENET, "Failed to Add handler(%x, %x): Too many handlers", handlerPtr, handlerArg);
			retval = ERROR_NET_ADHOCCTL_TOO_MANY_HANDLERS; // TODO: What's the proper error code for Apctl's TOO_MANY_HANDLERS?
			return retval;
		}
		apctlHandlers[retval] = handler;
		DEBUG_LOG(SCENET, "Added Apctl handler(%x, %x): %d", handlerPtr, handlerArg, retval);
	}
	else {
		ERROR_LOG(SCENET, "Existing Apctl handler(%x, %x)", handlerPtr, handlerArg);
	}

	// The id to return is the number of handlers currently registered
	return retval;
}

// TODO: How many handlers can the PSP actually have for Apctl?
// TODO: Should we allow the same handler to be added more than once?
static u32 sceNetApctlAddHandler(u32 handlerPtr, u32 handlerArg) {
	INFO_LOG(SCENET, "%s(%08x, %08x)", __FUNCTION__, handlerPtr, handlerArg);
	return NetApctl_AddHandler(handlerPtr, handlerArg);
}

int NetApctl_DelHandler(u32 handlerID) {
	if (apctlHandlers.find(handlerID) != apctlHandlers.end()) {
		apctlHandlers.erase(handlerID);
		WARN_LOG(SCENET, "Deleted Apctl handler: %d", handlerID);
	}
	else {
		ERROR_LOG(SCENET, "Invalid Apctl handler: %d", handlerID);
	}
	return 0;
}

static int sceNetApctlDelHandler(u32 handlerID) {
	INFO_LOG(SCENET, "%s(%d)", __FUNCTION__, handlerID);
	return NetApctl_DelHandler(handlerID);
}

static int sceNetInetInetPton(int af, const char* hostname, u32 inAddrPtr) {
	WARN_LOG(SCENET, "UNTESTED sceNetInetInetPton(%i, %s, %08x)", af, safe_string(hostname), inAddrPtr);
	if (!Memory::IsValidAddress(inAddrPtr)) {
		return hleLogError(SCENET, 0, "invalid arg"); //-1
	}

	int retval = inet_pton(convertSocketDomainPSP2Host(af), hostname, (void*)Memory::GetPointer(inAddrPtr));
	return hleLogSuccessI(SCENET, retval);
}

static int sceNetInetInetAton(const char* hostname, u32 inAddrPtr) {
	WARN_LOG(SCENET, "UNTESTED sceNetInetInetAton(%s, %08x)", safe_string(hostname), inAddrPtr);
	if (!Memory::IsValidAddress(inAddrPtr)) {
		return hleLogError(SCENET, 0, "invalid arg"); //-1
	}

	int retval = inet_pton(AF_INET, hostname, (void*)Memory::GetPointer(inAddrPtr));
	// inet_aton() returns nonzero if the address is valid, zero if not.
	return hleLogSuccessI(SCENET, retval);
}

// TODO: Need to find out whether it's possible to get partial output or not, since Coded Arms Contagion is using a small bufsize(4)
static u32 sceNetInetInetNtop(int af, u32 srcInAddrPtr, u32 dstBufPtr, u32 bufsize) {
	WARN_LOG(SCENET, "UNTESTED sceNetInetInetNtop(%i, %08x, %08x, %d)", af, srcInAddrPtr, dstBufPtr, bufsize);
	if (!Memory::IsValidAddress(srcInAddrPtr)) {
		return hleLogError(SCENET, 0, "invalid arg");
	}
	if (!Memory::IsValidAddress(dstBufPtr) || bufsize < 1/*8*/) { // usually 8 or 16, but Coded Arms Contagion is using bufsize = 4
		inetLastErrno = ENOSPC;
		return hleLogError(SCENET, 0, "invalid arg");
	}

	if (inet_ntop(convertSocketDomainPSP2Host(af), Memory::GetCharPointer(srcInAddrPtr), (char*)Memory::GetCharPointer(dstBufPtr), bufsize) == NULL) {
		//return hleLogDebug(SCENET, 0, "invalid arg?"); // Temporarily commented out in case it's allowed to have partial output
	}
	return hleLogSuccessX(SCENET, dstBufPtr, "%s", safe_string(Memory::GetCharPointer(dstBufPtr)));
}

static u32_le sceNetInetInetAddr(const char* hostname) {
	WARN_LOG(SCENET, "UNTESTED sceNetInetInetAddr(%s)", safe_string(hostname));
	if (hostname == nullptr || hostname[0]=='\0')
		return hleLogError(SCENET, INADDR_NONE, "invalid arg");

	u32 retval = INADDR_NONE; // inet_addr(hostname); // deprecated?
	inet_pton(AF_INET, hostname, &retval); // Alternative to the deprecated inet_addr

	return hleLogSuccessX(SCENET, retval);
}

static int sceNetInetGetpeername(int sock, u32 namePtr, u32 namelenPtr) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %08x, %08x)", __FUNCTION__, sock, namePtr, namelenPtr);
	if (!Memory::IsValidAddress(namePtr) || !Memory::IsValidAddress(namelenPtr)) {
		inetLastErrno = EFAULT;
		return hleLogError(SCENET, -1, "invalid arg");
	}

	SceNetInetSockaddr* name = (SceNetInetSockaddr*)Memory::GetPointer(namePtr);
	int* namelen = (int*)Memory::GetPointer(namelenPtr);
	SockAddrIN4 saddr{};
	// TODO: Should've created convertSockaddrPSP2Host (and Host2PSP too) function as it's being used pretty often, thus fixing a bug on it will be tedious when scattered all over the places
	saddr.addr.sa_family = name->sa_family;
	int len = std::min(*namelen > 0 ? *namelen : 0, static_cast<int>(sizeof(saddr)));
	memcpy(saddr.addr.sa_data, name->sa_data, sizeof(name->sa_data));
	int retval = getpeername(sock, (sockaddr*)&saddr, (socklen_t*)&len);
	DEBUG_LOG(SCENET, "Getpeername: Family = %s, Address = %s, Port = %d", inetSocketDomain2str(saddr.addr.sa_family).c_str(), ip2str(saddr.in.sin_addr).c_str(), ntohs(saddr.in.sin_port));
	*namelen = len;
	if (retval < 0) {
		inetLastErrno = errno;
		return hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
	}
	else {
		memcpy(name->sa_data, saddr.addr.sa_data, len-(sizeof(name->sa_len)+sizeof(name->sa_family)));
		name->sa_len = len;
		name->sa_family = saddr.addr.sa_family;
	}
	return 0;
}

static int sceNetInetGetsockname(int sock, u32 namePtr, u32 namelenPtr) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %08x, %08x)", __FUNCTION__, sock, namePtr, namelenPtr);
	if (!Memory::IsValidAddress(namePtr) || !Memory::IsValidAddress(namelenPtr)) {
		inetLastErrno = EFAULT;
		return hleLogError(SCENET, -1, "invalid arg");
	}

	SceNetInetSockaddr* name = (SceNetInetSockaddr*)Memory::GetPointer(namePtr);
	int* namelen = (int*)Memory::GetPointer(namelenPtr);
	SockAddrIN4 saddr{};
	saddr.addr.sa_family = name->sa_family;
	int len = std::min(*namelen > 0 ? *namelen : 0, static_cast<int>(sizeof(saddr)));
	memcpy(saddr.addr.sa_data, name->sa_data, sizeof(name->sa_data));
	int retval = getsockname(sock, (sockaddr*)&saddr, (socklen_t*)&len);
	DEBUG_LOG(SCENET, "Getsockname: Family = %s, Address = %s, Port = %d", inetSocketDomain2str(saddr.addr.sa_family).c_str(), ip2str(saddr.in.sin_addr).c_str(), ntohs(saddr.in.sin_port));
	*namelen = len;
	if (retval < 0) {
		inetLastErrno = errno;
		return hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
	}
	else {
		memcpy(name->sa_data, saddr.addr.sa_data, len - (sizeof(name->sa_len) + sizeof(name->sa_family)));
		name->sa_len = len;
		name->sa_family = saddr.addr.sa_family;
	}
	return 0;
}

// FIXME: nfds is number of fd(s) as in posix poll, or was it maximum fd value as in posix select? Star Wars Battlefront Renegade seems to set the nfds to 64, while Coded Arms Contagion is using 256
int sceNetInetSelect(int nfds, u32 readfdsPtr, u32 writefdsPtr, u32 exceptfdsPtr, u32 timeoutPtr) {
	DEBUG_LOG(SCENET, "UNTESTED sceNetInetSelect(%i, %08x, %08x, %08x, %08x) at %08x", nfds, readfdsPtr, writefdsPtr, exceptfdsPtr, timeoutPtr, currentMIPS->pc);
	int retval = -1;
	SceNetInetFdSet* readfds = (SceNetInetFdSet*)Memory::GetCharPointer(readfdsPtr);
	SceNetInetFdSet* writefds = (SceNetInetFdSet*)Memory::GetCharPointer(writefdsPtr);
	SceNetInetFdSet* exceptfds = (SceNetInetFdSet*)Memory::GetCharPointer(exceptfdsPtr);
	SceNetInetTimeval* timeout = (SceNetInetTimeval*)Memory::GetCharPointer(timeoutPtr);
	// TODO: Use poll instead of select since Windows' FD_SETSIZE is only 64 while PSP is 256, and select can only work for fd value less than FD_SETSIZE on some system
	fd_set rdfds{}, wrfds{}, exfds{};
	FD_ZERO(&rdfds); FD_ZERO(&wrfds); FD_ZERO(&exfds);
	int maxfd = nfds; // (nfds > PSP_NET_INET_FD_SETSIZE) ? nfds : PSP_NET_INET_FD_SETSIZE;
	int rdcnt = 0, wrcnt = 0, excnt = 0;
	for (int i = maxfd - 1; i >= 0 /*&& i >= maxfd - 64*/; i--) {
		bool windows_workaround = false;
#if PPSSPP_PLATFORM(WINDOWS)
		//windows_workaround = (i == nfds - 1);
#endif
		if (readfds != NULL && (NetInetFD_ISSET(i, readfds) || windows_workaround)) {
			VERBOSE_LOG(SCENET, "Input Read FD #%i", i);
			if (rdcnt < FD_SETSIZE) {
				FD_SET(i, &rdfds); // This might pointed to a non-existing socket or sockets belonged to other programs on Windows, because most of the time Windows socket have an id above 1k instead of 0-255
				rdcnt++;
			}
		}
		if (writefds != NULL && (NetInetFD_ISSET(i, writefds) || windows_workaround)) {
			VERBOSE_LOG(SCENET, "Input Write FD #%i", i);
			if (wrcnt < FD_SETSIZE) {
				FD_SET(i, &wrfds);
				wrcnt++;
			}
		}
		if (exceptfds != NULL && (NetInetFD_ISSET(i, exceptfds) || windows_workaround)) {
			VERBOSE_LOG(SCENET, "Input Except FD #%i", i);
			if (excnt < FD_SETSIZE) {
				FD_SET(i, &exfds);
				excnt++;
			}
		}
	}
	// Workaround for games that set ndfs to 64 instead of socket id + 1
	if (inetLastSocket >= 0) {
		if (readfds != NULL && rdcnt == 0) {
			FD_SET(inetLastSocket, &rdfds);
			rdcnt++;
		}
		if (writefds != NULL && wrcnt == 0) {
			FD_SET(inetLastSocket, &wrfds);
			wrcnt++;
		}
		if (exceptfds != NULL && excnt == 0) {
			FD_SET(inetLastSocket, &exfds);
			excnt++;
		}
	}

	timeval tmout = {5, 543210}; // Workaround timeout value when timeout = NULL
	if (timeout != NULL) {
		tmout.tv_sec = timeout->tv_sec;
		tmout.tv_usec = timeout->tv_usec;
	}
	VERBOSE_LOG(SCENET, "Select: Read count: %d, Write count: %d, Except count: %d, TimeVal: %u.%u", rdcnt, wrcnt, excnt, tmout.tv_sec, tmout.tv_usec);
	// TODO: Simulate blocking behaviour when timeout = NULL to prevent PPSSPP from freezing
	retval = select(nfds, (readfds == NULL) ? NULL: &rdfds, (writefds  == NULL) ? NULL: &wrfds, (exceptfds == NULL) ? NULL: &exfds, /*(timeout == NULL) ? NULL :*/ &tmout);
	if (readfds != NULL && inetLastSocket < maxfd) NetInetFD_ZERO(readfds); // Clear it only when not needing a workaround
	if (writefds != NULL && inetLastSocket < maxfd) NetInetFD_ZERO(writefds); // Clear it only when not needing a workaround
	if (exceptfds != NULL) NetInetFD_ZERO(exceptfds);
	for (int i = maxfd - 1; i >= 0 /*&& i >= maxfd - 64*/; i--) {
		if (readfds != NULL && FD_ISSET(i, &rdfds))
			NetInetFD_SET(i, readfds);
		if (writefds != NULL && FD_ISSET(i, &wrfds))
			NetInetFD_SET(i, writefds);
		if (exceptfds != NULL && FD_ISSET(i, &exfds))
			NetInetFD_SET(i, exceptfds);
	}
	// Workaround for games that set ndfs to 64 instead of socket id + 1
	if (inetLastSocket >= 0) {
		if (readfds != NULL && rdcnt == 1 && FD_ISSET(inetLastSocket, &rdfds))
			NetInetFD_SET(inetLastSocket, readfds);
		if (writefds != NULL && wrcnt == 1 && FD_ISSET(inetLastSocket, &wrfds))
			NetInetFD_SET(inetLastSocket, writefds);
		if (exceptfds != NULL && excnt == 1 && FD_ISSET(inetLastSocket, &exfds))
			NetInetFD_SET(inetLastSocket, exceptfds);
	}

	if (retval < 0) {
		inetLastErrno = errno;
		if (inetLastErrno == 0)
			hleLogDebug(SCENET, retval, "errno = %d", inetLastErrno);
		else if (inetLastErrno < 0)
			hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
		return hleLogDebug(SCENET, hleDelayResult(retval, "workaround until blocking-socket", 500)); // Using hleDelayResult as a workaround for games that need blocking-socket to be implemented (ie. Coded Arms Contagion)
	}
	return hleLogSuccessI(SCENET, hleDelayResult(retval, "workaround until blocking-socket", 500)); // Using hleDelayResult as a workaround for games that need blocking-socket to be implemented (ie. Coded Arms Contagion)
}

int sceNetInetPoll(u32 fdsPtr, u32 nfds, int timeout) { // timeout in miliseconds just like posix poll? or in microseconds as other PSP timeout?
	DEBUG_LOG(SCENET, "UNTESTED sceNetInetPoll(%08x, %d, %i) at %08x", fdsPtr, nfds, timeout, currentMIPS->pc);
	int retval = -1;
	int maxfd = 0;
	SceNetInetPollfd *fdarray = (SceNetInetPollfd*)Memory::GetPointer(fdsPtr); // SceNetInetPollfd/pollfd, sceNetInetPoll() have similarity to BSD poll() but pollfd have different size on 64bit

	if (nfds > FD_SETSIZE)
		nfds = FD_SETSIZE;

	fd_set readfds{}, writefds{}, exceptfds{};
	FD_ZERO(&readfds); FD_ZERO(&writefds); FD_ZERO(&exceptfds);
	for (int i = 0; i < (s32)nfds; i++) {
		if (fdarray[i].fd < 0) {
			inetLastErrno = EINVAL;
			return hleLogError(SCENET, -1, "invalid socket id");
		}
		if (fdarray[i].fd > maxfd) maxfd = fdarray[i].fd;
		FD_SET(fdarray[i].fd, &readfds);
		FD_SET(fdarray[i].fd, &writefds);
		FD_SET(fdarray[i].fd, &exceptfds); 
		fdarray[i].revents = 0;
	}
	timeval tmout = { 5, 543210 }; // Workaround timeout value when timeout = NULL
	if (timeout >= 0) {
		tmout.tv_sec = timeout / 1000000; // seconds
		tmout.tv_usec = (timeout % 1000000); // microseconds
	}
	// TODO: Simulate blocking behaviour when timeout is non-zero to prevent PPSSPP from freezing
	retval = select(maxfd + 1, &readfds, &writefds, &exceptfds, /*(timeout<0)? NULL:*/&tmout);
	if (retval < 0) {
		inetLastErrno = EINTR;
		return hleLogError(SCENET, hleDelayResult(retval, "workaround until blocking-socket", 500)); // Using hleDelayResult as a workaround for games that need blocking-socket to be implemented
	}

	retval = 0;
	for (int i = 0; i < (s32)nfds; i++) {
		if ((fdarray[i].events & (INET_POLLRDNORM | INET_POLLIN)) && FD_ISSET(fdarray[i].fd, &readfds))
		    fdarray[i].revents |= (INET_POLLRDNORM | INET_POLLIN); //POLLIN_SET
		if ((fdarray[i].events & (INET_POLLWRNORM | INET_POLLOUT)) && FD_ISSET(fdarray[i].fd, &writefds))
		    fdarray[i].revents |= (INET_POLLWRNORM | INET_POLLOUT); //POLLOUT_SET
		fdarray[i].revents &= fdarray[i].events;
		if (FD_ISSET(fdarray[i].fd, &exceptfds)) 
			fdarray[i].revents |= (INET_POLLRDBAND | INET_POLLPRI | INET_POLLERR); //POLLEX_SET; // Can be raised on revents regardless of events bitmask?
		if (fdarray[i].revents) 
			retval++;
		VERBOSE_LOG(SCENET, "Poll Socket#%d Fd: %d, events: %04x, revents: %04x, availToRecv: %d", i, fdarray[i].fd, fdarray[i].events, fdarray[i].revents, getAvailToRecv(fdarray[i].fd));
	}
	//hleEatMicro(1000);
	return hleLogSuccessI(SCENET, hleDelayResult(retval, "workaround until blocking-socket", 1000)); // Using hleDelayResult as a workaround for games that need blocking-socket to be implemented
}

static int sceNetInetRecv(int socket, u32 bufPtr, u32 bufLen, u32 flags) {
	DEBUG_LOG(SCENET, "UNTESTED sceNetInetRecv(%i, %08x, %i, %08x) at %08x", socket, bufPtr, bufLen, flags, currentMIPS->pc);
	int flgs = flags & ~PSP_NET_INET_MSG_DONTWAIT; // removing non-POSIX flag, which is an alternative way to use non-blocking mode
	flgs = convertMSGFlagsPSP2Host(flgs);
	int retval = recv(socket, (char*)Memory::GetPointer(bufPtr), bufLen, flgs | MSG_NOSIGNAL);
	if (retval < 0) {
		inetLastErrno = errno;
		if (inetLastErrno == EAGAIN) 
			hleLogDebug(SCENET, retval, "errno = %d", inetLastErrno);
		else
			hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
		return hleDelayResult(retval, "workaround until blocking-socket", 500); // Using hleDelayResult as a workaround for games that need blocking-socket to be implemented
	}

	std::string datahex;
	DataToHexString(10, 0, Memory::GetPointer(bufPtr), retval, &datahex);
	VERBOSE_LOG(SCENET, "Data Dump (%d bytes):\n%s", retval, datahex.c_str());

	return hleLogSuccessInfoI(SCENET, hleDelayResult(retval, "workaround until blocking-socket", 500)); // Using hleDelayResult as a workaround for games that need blocking-socket to be implemented
}

static int sceNetInetSend(int socket, u32 bufPtr, u32 bufLen, u32 flags) {
	DEBUG_LOG(SCENET, "UNTESTED sceNetInetSend(%i, %08x, %i, %08x) at %08x", socket, bufPtr, bufLen, flags, currentMIPS->pc);

	std::string datahex;
	DataToHexString(10, 0, Memory::GetPointer(bufPtr), bufLen, &datahex);
	VERBOSE_LOG(SCENET, "Data Dump (%d bytes):\n%s", bufLen, datahex.c_str());

	int flgs = flags & ~PSP_NET_INET_MSG_DONTWAIT; // removing non-POSIX flag, which is an alternative way to use non-blocking mode
	flgs = convertMSGFlagsPSP2Host(flgs);
	int retval = send(socket, (char*)Memory::GetPointer(bufPtr), bufLen, flgs | MSG_NOSIGNAL);

	if (retval < 0) {
		inetLastErrno = errno;
		if (inetLastErrno == EAGAIN)
			hleLogDebug(SCENET, retval, "errno = %d", inetLastErrno);
		else
			hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
		return retval;
	}

	return hleLogSuccessInfoI(SCENET, retval);
}

static int sceNetInetSocket(int domain, int type, int protocol) {
	WARN_LOG(SCENET, "UNTESTED sceNetInetSocket(%i, %i, %i) at %08x", domain, type, protocol, currentMIPS->pc);
	DEBUG_LOG(SCENET, "Socket: Domain = %s, Type = %s, Protocol = %s", inetSocketDomain2str(domain).c_str(), inetSocketType2str(type).c_str(), inetSocketProto2str(protocol).c_str());
	int retval = socket(convertSocketDomainPSP2Host(domain), convertSocketTypePSP2Host(type), convertSocketProtoPSP2Host(protocol));
	if (retval < 0) {
		inetLastErrno = errno;
		return hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
	}

	//InetSocket* sock = new InetSocket(domain, type, protocol);
	//retval = pspSockets.Create(sock);

	// Ignore SIGPIPE when supported (ie. BSD/MacOS)
	setSockNoSIGPIPE(retval, 1);
	// TODO: We should always use non-blocking mode and simulate blocking mode
	changeBlockingMode(retval, 1);
	// Enable Port Re-use, required for multiple-instance
	setSockReuseAddrPort(retval);
	// Disable Connection Reset error on UDP to avoid strange behavior
	setUDPConnReset(retval, false);

	inetLastSocket = retval;
	return hleLogSuccessI(SCENET, retval);
}

static int sceNetInetSetsockopt(int socket, int level, int optname, u32 optvalPtr, int optlen) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %i, %i, %08x, %i) at %08x", __FUNCTION__, socket, level, optname, optvalPtr, optlen, currentMIPS->pc);
	u32_le* optval = (u32_le*)Memory::GetPointer(optvalPtr);
	DEBUG_LOG(SCENET, "SockOpt: Level = %s, OptName = %s, OptValue = %d", inetSockoptLevel2str(level).c_str(), inetSockoptName2str(optname, level).c_str(), *optval);
	timeval tval{};
	// InetSocket* sock = pspSockets.Get<InetSocket>(socket, error);
	// TODO: Ignoring SO_NBIO/SO_NONBLOCK flag if we always use non-bloking mode (ie. simulated blocking mode)
	if (level == PSP_NET_INET_SOL_SOCKET && optname == PSP_NET_INET_SO_NBIO) {
		//memcpy(&sock->nonblocking, (int*)optval, std::min(sizeof(sock->nonblocking), optlen));
		return hleLogSuccessI(SCENET, 0);
	}
	// FIXME: Should we ignore SO_BROADCAST flag since we are using fake broadcast (ie. only broadcast to friends), 
	//        But Infrastructure/Online play might need to use broadcast for SSDP and to support LAN MP with real PSP
	/*else if (level == PSP_NET_INET_SOL_SOCKET && optname == PSP_NET_INET_SO_BROADCAST) {
		//memcpy(&sock->so_broadcast, (int*)optval, std::min(sizeof(sock->so_broadcast), optlen));
		return hleLogSuccessI(SCENET, 0);
	}*/
	// TODO: Ignoring SO_REUSEADDR flag to prevent disrupting multiple-instance feature
	else if (level == PSP_NET_INET_SOL_SOCKET && optname == PSP_NET_INET_SO_REUSEADDR) {
		//memcpy(&sock->reuseaddr, (int*)optval, std::min(sizeof(sock->reuseaddr), optlen));
		return hleLogSuccessI(SCENET, 0);
	}
	// TODO: Ignoring SO_REUSEPORT flag to prevent disrupting multiple-instance feature (not sure if PSP has SO_REUSEPORT or not tho, defined as 15 on Android)
	else if (level == PSP_NET_INET_SOL_SOCKET && optname == PSP_NET_INET_SO_REUSEPORT) { // 15
		//memcpy(&sock->reuseport, (int*)optval, std::min(sizeof(sock->reuseport), optlen));
		return hleLogSuccessI(SCENET, 0);
	}
	// TODO: Ignoring SO_NOSIGPIPE flag to prevent crashing PPSSPP (not sure if PSP has NOSIGPIPE or not tho, defined as 0x1022 on Darwin)
	else if (level == PSP_NET_INET_SOL_SOCKET && optname == 0x1022) { // PSP_NET_INET_SO_NOSIGPIPE ?
		//memcpy(&sock->nosigpipe, (int*)optval, std::min(sizeof(sock->nosigpipe), optlen));
		return hleLogSuccessI(SCENET, 0);
	}
	// It seems UNO game will try to set socket buffer size with a very large size and ended getting error (-1), so we should also limit the buffer size to replicate PSP behavior
	else if (level == PSP_NET_INET_SOL_SOCKET && (optname == PSP_NET_INET_SO_RCVBUF || optname == PSP_NET_INET_SO_SNDBUF)) { // PSP_NET_INET_SO_NOSIGPIPE ?
		// TODO: For SOCK_STREAM max buffer size is 8 Mb on BSD, while max SOCK_DGRAM is 65535 minus the IP & UDP Header size
		if (*optval > 8 * 1024 * 1024) {
			inetLastErrno = ENOBUFS; // FIXME: return ENOBUFS for SOCK_STREAM, and EINVAL for SOCK_DGRAM
			return hleLogError(SCENET, -1, "buffer size too large?");
		}
	}
	int retval = 0;
	// PSP timeout are a single 32bit value (micro seconds)
	if (level == PSP_NET_INET_SOL_SOCKET &&  optval && (optname == PSP_NET_INET_SO_RCVTIMEO || optname == PSP_NET_INET_SO_SNDTIMEO)) { 
		tval.tv_sec = *optval / 1000000; // seconds
		tval.tv_usec = (*optval % 1000000); // microseconds
		retval = setsockopt(socket, convertSockoptLevelPSP2Host(level), convertSockoptNamePSP2Host(optname, level), (char*)&tval, sizeof(tval));
	}
	else {
		retval = setsockopt(socket, convertSockoptLevelPSP2Host(level), convertSockoptNamePSP2Host(optname, level), (char*)optval, optlen);
	}
	if (retval < 0) {
		inetLastErrno = errno;
		hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
	}
	return hleLogSuccessI(SCENET, retval);
}

static int sceNetInetGetsockopt(int socket, int level, int optname, u32 optvalPtr, u32 optlenPtr) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %i, %i, %08x, %08x) at %08x", __FUNCTION__, socket, level, optname, optvalPtr, optlenPtr, currentMIPS->pc);
	u32_le* optval = (u32_le*)Memory::GetPointer(optvalPtr);
    socklen_t* optlen = (socklen_t*)Memory::GetPointer(optlenPtr);
	DEBUG_LOG(SCENET, "SockOpt: Level = %s, OptName = %s", inetSockoptLevel2str(level).c_str(), inetSockoptName2str(optname, level).c_str());
	timeval tval{};
	// InetSocket* sock = pspSockets.Get<InetSocket>(socket, error);
	// TODO: Ignoring SO_NBIO/SO_NONBLOCK flag if we always use non-bloking mode (ie. simulated blocking mode)
	if (level == PSP_NET_INET_SOL_SOCKET && optname == PSP_NET_INET_SO_NBIO) {
		//*optlen = std::min(sizeof(sock->nonblocking), *optlen);
		//memcpy((int*)optval, &sock->nonblocking, *optlen); 
		//if (sock->nonblocking && *optlen>0) *optval = 0x80; // on true, returning 0x80 when retrieved using getsockopt?
		return hleLogSuccessI(SCENET, 0);
	}
	// FIXME: Should we ignore SO_BROADCAST flag since we are using fake broadcast (ie. only broadcast to friends), 
	//        But Infrastructure/Online play might need to use broadcast for SSDP and to support LAN MP with real PSP
	/*else if (level == PSP_NET_INET_SOL_SOCKET && optname == PSP_NET_INET_SO_BROADCAST) {
		//*optlen = std::min(sizeof(sock->so_broadcast), *optlen);
		//memcpy((int*)optval, &sock->so_broadcast, *optlen); 
		//if (sock->so_broadcast && *optlen>0) *optval = 0x80; // on true, returning 0x80 when retrieved using getsockopt?
		return hleLogSuccessI(SCENET, 0);
	}*/
	// TODO: Ignoring SO_REUSEADDR flag to prevent disrupting multiple-instance feature
	else if (level == PSP_NET_INET_SOL_SOCKET && optname == PSP_NET_INET_SO_REUSEADDR) {
		//*optlen = std::min(sizeof(sock->reuseaddr), *optlen);
		//memcpy((int*)optval, &sock->reuseaddr, *optlen);
		return hleLogSuccessI(SCENET, 0);
	}
	// TODO: Ignoring SO_REUSEPORT flag to prevent disrupting multiple-instance feature (not sure if PSP has SO_REUSEPORT or not tho, defined as 15 on Android)
	else if (level == PSP_NET_INET_SOL_SOCKET && optname == PSP_NET_INET_SO_REUSEPORT) { // 15
		//*optlen = std::min(sizeof(sock->reuseport), *optlen);
		//memcpy((int*)optval, &sock->reuseport, *optlen);
		return hleLogSuccessI(SCENET, 0);
	}
	// TODO: Ignoring SO_NOSIGPIPE flag to prevent crashing PPSSPP (not sure if PSP has NOSIGPIPE or not tho, defined as 0x1022 on Darwin)
	else if (level == PSP_NET_INET_SOL_SOCKET && optname == 0x1022) { // PSP_NET_INET_SO_NOSIGPIPE ?
		//*optlen = std::min(sizeof(sock->nosigpipe), *optlen);
		//memcpy((int*)optval, &sock->nosigpipe, *optlen);
		return hleLogSuccessI(SCENET, 0);
	}
	int retval = 0;
	// PSP timeout are a single 32bit value (micro seconds)
	if (level == PSP_NET_INET_SOL_SOCKET && optval && (optname == PSP_NET_INET_SO_RCVTIMEO || optname == PSP_NET_INET_SO_SNDTIMEO)) {
		socklen_t tvlen = sizeof(tval);
		retval = getsockopt(socket, convertSockoptLevelPSP2Host(level), convertSockoptNamePSP2Host(optname, level), (char*)&tval, &tvlen);
		if (retval != SOCKET_ERROR) {
			u64_le val = (tval.tv_sec * 1000000LL) + tval.tv_usec;
			memcpy(optval, &val, std::min(static_cast<socklen_t>(sizeof(val)), std::min(static_cast<socklen_t>(sizeof(*optval)), *optlen)));
		}
	}
	else {
		retval = getsockopt(socket, convertSockoptLevelPSP2Host(level), convertSockoptNamePSP2Host(optname, level), (char*)optval, optlen);
	}
	if (retval < 0) {
		inetLastErrno = errno;
		hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
	}
	DEBUG_LOG(SCENET, "SockOpt: OptValue = %d", *optval);
	return hleLogSuccessI(SCENET, retval);
}

static int sceNetInetBind(int socket, u32 namePtr, int namelen) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %08x, %i) at %08x", __FUNCTION__, socket, namePtr, namelen, currentMIPS->pc);
	SceNetInetSockaddr* name = (SceNetInetSockaddr*)Memory::GetPointer(namePtr);
	SockAddrIN4 saddr{};
	// TODO: Should've created convertSockaddrPSP2Host (and Host2PSP too) function as it's being used pretty often, thus fixing a bug on it will be tedious when scattered all over the places
	saddr.addr.sa_family = name->sa_family;
	int len = std::min(namelen > 0 ? namelen : 0, static_cast<int>(sizeof(saddr)));
	memcpy(saddr.addr.sa_data, name->sa_data, sizeof(name->sa_data));
	if (isLocalServer) {
		getLocalIp(&saddr.in);
	}
	// FIXME: On non-Windows broadcast to INADDR_BROADCAST(255.255.255.255) might not be received by the sender itself when binded to specific IP (ie. 192.168.0.2) or INADDR_BROADCAST.
	//        Meanwhile, it might be received by itself when binded to subnet (ie. 192.168.0.255) or INADDR_ANY(0.0.0.0).
	if (saddr.in.sin_addr.s_addr == INADDR_ANY || saddr.in.sin_addr.s_addr == INADDR_BROADCAST) {
		// Replace INADDR_ANY with a specific IP in order not to send data through the wrong interface (especially during broadcast)
		// Get Local IP Address
		sockaddr_in sockAddr{};
		getLocalIp(&sockAddr);
		DEBUG_LOG(SCENET, "Bind: Address Replacement = %s => %s", ip2str(saddr.in.sin_addr).c_str(), ip2str(sockAddr.sin_addr).c_str());
		saddr.in.sin_addr.s_addr = sockAddr.sin_addr.s_addr;
	}
	// TODO: Make use Port Offset only for PPSSPP to PPSSPP communications (ie. IP addresses available in the group/friendlist), otherwise should be considered as Online Service thus should use the port as is.
	//saddr.in.sin_port = htons(ntohs(saddr.in.sin_port) + portOffset);
	DEBUG_LOG(SCENET, "Bind: Family = %s, Address = %s, Port = %d", inetSocketDomain2str(saddr.addr.sa_family).c_str(), ip2str(saddr.in.sin_addr).c_str(), ntohs(saddr.in.sin_port));
	changeBlockingMode(socket, 0);
	int retval = bind(socket, (struct sockaddr*)&saddr, len);
	if (retval < 0) {
		inetLastErrno = errno;
		changeBlockingMode(socket, 1);
		return hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
	}
	changeBlockingMode(socket, 1);
	// Update binded port number if it was 0 (any port)
	memcpy(name->sa_data, saddr.addr.sa_data, sizeof(name->sa_data));
	// Enable Port-forwarding
	// TODO: Check the socket type/protocol for SOCK_STREAM/SOCK_DGRAM or IPPROTO_TCP/IPPROTO_UDP instead of forwarding both protocol
	// InetSocket* sock = pspSockets.Get<InetSocket>(socket, error);
	// UPnP_Add((sock->type == SOCK_STREAM)? IP_PROTOCOL_TCP: IP_PROTOCOL_UDP, port, port);	
	unsigned short port = ntohs(saddr.in.sin_port);
	UPnP_Add(IP_PROTOCOL_UDP, port, port);
	UPnP_Add(IP_PROTOCOL_TCP, port, port);

	// Workaround: Send a dummy 0 size message to AdhocServer IP to make sure the socket actually bound to an address when binded with INADDR_ANY before using getsockname, seems to fix sending DGRAM from incorrect port issue on Android
	/*saddr.in.sin_addr.s_addr = g_adhocServerIP.in.sin_addr.s_addr;
	saddr.in.sin_port = 0;
	sendto(socket, dummyPeekBuf64k, 0, MSG_NOSIGNAL, (struct sockaddr*)&saddr, sizeof(saddr));
	*/

	return hleLogSuccessI(SCENET, retval);
}

static int sceNetInetConnect(int socket, u32 sockAddrPtr, int sockAddrLen) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %08x, %i) at %08x", __FUNCTION__, socket, sockAddrPtr, sockAddrLen, currentMIPS->pc);
	SceNetInetSockaddr* dst = (SceNetInetSockaddr*)Memory::GetPointer(sockAddrPtr);
	SockAddrIN4 saddr{};
	int dstlen = std::min(sockAddrLen > 0 ? sockAddrLen : 0, static_cast<int>(sizeof(saddr)));
	saddr.addr.sa_family = dst->sa_family;
	memcpy(saddr.addr.sa_data, dst->sa_data, sizeof(dst->sa_data));
	DEBUG_LOG(SCENET, "Connect: Address = %s, Port = %d", ip2str(saddr.in.sin_addr).c_str(), ntohs(saddr.in.sin_port));

	// Workaround to avoid blocking for indefinitely
	setSockTimeout(socket, SO_SNDTIMEO, 5000000);
	setSockTimeout(socket, SO_RCVTIMEO, 5000000);
	changeBlockingMode(socket, 0); // Use blocking mode as temporary fix for UNO, since we don't simulate blocking-mode yet
	int retval = connect(socket, (struct sockaddr*)&saddr.addr, dstlen);
	if (retval < 0) {
		inetLastErrno = errno;
		if (connectInProgress(inetLastErrno))
			hleLogDebug(SCENET, retval, "errno = %d", inetLastErrno);
		else
			hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
		changeBlockingMode(socket, 1);
		// TODO: Since we're temporarily forcing blocking-mode we'll need to change errno from ETIMEDOUT to EAGAIN
		/*if (inetLastErrno == ETIMEDOUT)
			inetLastErrno = EAGAIN;
		*/
		return hleLogDebug(SCENET, retval);
	}
	changeBlockingMode(socket, 1);

	return hleLogSuccessI(SCENET, retval);
}

static int sceNetInetListen(int socket, int backlog) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %i) at %08x", __FUNCTION__, socket, backlog, currentMIPS->pc);

	int retval = listen(socket, (backlog == PSP_NET_INET_SOMAXCONN? SOMAXCONN : backlog));
	if (retval < 0) {
		inetLastErrno = errno;
		return hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
	}

	return hleLogSuccessI(SCENET, retval);
}

static int sceNetInetAccept(int socket, u32 addrPtr, u32 addrLenPtr) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %08x, %08x) at %08x", __FUNCTION__, socket, addrPtr, addrLenPtr, currentMIPS->pc);
	SceNetInetSockaddr* src = (SceNetInetSockaddr*)Memory::GetCharPointer(addrPtr);
	socklen_t* srclen = (socklen_t*)Memory::GetCharPointer(addrLenPtr);
	SockAddrIN4 saddr{};
	if (srclen)
		*srclen = std::min((*srclen) > 0 ? *srclen : 0, static_cast<socklen_t>(sizeof(saddr)));
	int retval = accept(socket, (struct sockaddr*)&saddr.addr, srclen);
	if (retval < 0) {
		inetLastErrno = errno;
		if (inetLastErrno == EAGAIN)
			hleLogDebug(SCENET, retval, "errno = %d", inetLastErrno);
		else
			hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
		return retval;
	}

	if (src) {
		src->sa_family = saddr.addr.sa_family;
		memcpy(src->sa_data, saddr.addr.sa_data, sizeof(src->sa_data));
		src->sa_len = srclen? *srclen : 0;
	}
	DEBUG_LOG(SCENET, "Accept: Address = %s, Port = %d", ip2str(saddr.in.sin_addr).c_str(), ntohs(saddr.in.sin_port));
	
	return hleLogSuccessI(SCENET, retval);
}

static int sceNetInetShutdown(int socket, int how) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %i) at %08x", __FUNCTION__, socket, how, currentMIPS->pc);
	// Convert HOW from PSP to Host
	int hostHow = how;
	switch (how) {
	case PSP_NET_INET_SHUT_RD: hostHow = SHUT_RD; break;
	case PSP_NET_INET_SHUT_WR: hostHow = SHUT_WR; break;
	case PSP_NET_INET_SHUT_RDWR: hostHow = SHUT_RDWR; break;
	}
	return hleLogSuccessI(SCENET, shutdown(socket, hostHow));
}

static int sceNetInetSocketAbort(int socket) {
	WARN_LOG(SCENET, "UNTESTED %s(%i)", __FUNCTION__, socket);
	// FIXME: either using shutdown/close or select? probably using select if blocking mode is being simulated with non-blocking
	return hleLogSuccessI(SCENET, shutdown(socket, SHUT_RDWR));
}

static int sceNetInetClose(int socket) {
	WARN_LOG(SCENET, "UNTESTED %s(%i) at %08x", __FUNCTION__, socket, currentMIPS->pc);
	return hleLogSuccessI(SCENET, closesocket(socket));
}

static int sceNetInetCloseWithRST(int socket) {
	WARN_LOG(SCENET, "UNTESTED %s(%i) at %08x", __FUNCTION__, socket, currentMIPS->pc);
	// Based on http://deepix.github.io/2016/10/21/tcprst.html
	struct linger sl{};
	sl.l_onoff = 1;		// non-zero value enables linger option in kernel 
	sl.l_linger = 0;	// timeout interval in seconds 
	setsockopt(socket, SOL_SOCKET, SO_LINGER, (const char*)&sl, sizeof(sl));
	return hleLogSuccessI(SCENET, closesocket(socket));
}

static int sceNetInetRecvfrom(int socket, u32 bufferPtr, int len, int flags, u32 fromPtr, u32 fromlenPtr) {
	DEBUG_LOG(SCENET, "UNTESTED %s(%i, %08x, %i, %08x, %08x, %08x) at %08x", __FUNCTION__, socket, bufferPtr, len, flags, fromPtr, fromlenPtr, currentMIPS->pc);
	SceNetInetSockaddr* src = (SceNetInetSockaddr*)Memory::GetCharPointer(fromPtr);
    socklen_t* srclen = (socklen_t*)Memory::GetCharPointer(fromlenPtr);
	SockAddrIN4 saddr{};
	if (srclen)
		*srclen = std::min((*srclen) > 0? *srclen: 0, static_cast<socklen_t>(sizeof(saddr)));
	int flgs = flags & ~PSP_NET_INET_MSG_DONTWAIT; // removing non-POSIX flag, which is an alternative way to use non-blocking mode
	flgs = convertMSGFlagsPSP2Host(flgs);
	int retval = recvfrom(socket, (char*)Memory::GetPointer(bufferPtr), len, flgs | MSG_NOSIGNAL, (struct sockaddr*)&saddr.addr, srclen);
	if (retval < 0) {
		inetLastErrno = errno;
		if (inetLastErrno == EAGAIN)
			hleLogDebug(SCENET, retval, "errno = %d", inetLastErrno);
		else
			hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
		return hleDelayResult(retval, "workaround until blocking-socket", 500); // Using hleDelayResult as a workaround for games that need blocking-socket to be implemented (ie. Coded Arms Contagion)
	}
	
	if (src) {
		src->sa_family = saddr.addr.sa_family;
		memcpy(src->sa_data, saddr.addr.sa_data, sizeof(src->sa_data));
		src->sa_len = srclen ? *srclen : 0;
	}
	DEBUG_LOG(SCENET, "RecvFrom: Address = %s, Port = %d", ip2str(saddr.in.sin_addr).c_str(), ntohs(saddr.in.sin_port));

	// Discard if it came from APIPA address (ie. self-received broadcasts from 169.254.x.x when broadcasting to INADDR_BROADCAST on Windows) on Untold Legends The Warrior's Code / Twisted Metal Head On
	/*if (isAPIPA(saddr.in.sin_addr.s_addr)) {
		inetLastErrno = EAGAIN;
		retval = -1;
		DEBUG_LOG(SCENET, "RecvFrom: Ignoring Address = %s", ip2str(saddr.in.sin_addr).c_str());
		hleLogDebug(SCENET, retval, "faked errno = %d", inetLastErrno);
		return hleDelayResult(retval, "workaround until blocking-socket", 500);
	}*/

	std::string datahex;
	DataToHexString(0, 0, Memory::GetPointer(bufferPtr), retval, &datahex);
	VERBOSE_LOG(SCENET, "Data Dump (%d bytes):\n%s", retval, datahex.c_str());

	return hleLogSuccessInfoI(SCENET, hleDelayResult(retval, "workaround until blocking-socket", 500)); // Using hleDelayResult as a workaround for games that need blocking-socket to be implemented (ie. Coded Arms Contagion)
}

static int sceNetInetSendto(int socket, u32 bufferPtr, int len, int flags, u32 toPtr, int tolen) {
	DEBUG_LOG(SCENET, "UNTESTED %s(%i, %08x, %i, %08x, %08x, %d) at %08x", __FUNCTION__, socket, bufferPtr, len, flags, toPtr, tolen, currentMIPS->pc);
	SceNetInetSockaddr* dst = (SceNetInetSockaddr*)Memory::GetCharPointer(toPtr);
	int flgs = flags & ~PSP_NET_INET_MSG_DONTWAIT; // removing non-POSIX flag, which is an alternative way to use non-blocking mode
	flgs = convertMSGFlagsPSP2Host(flgs);
	SockAddrIN4 saddr{};
	int dstlen = std::min(tolen > 0? tolen: 0, static_cast<int>(sizeof(saddr)));
	if (dst) {
		saddr.addr.sa_family = dst->sa_family;
		memcpy(saddr.addr.sa_data, dst->sa_data, sizeof(dst->sa_data));
	}
	DEBUG_LOG(SCENET, "SendTo: Address = %s, Port = %d", ip2str(saddr.in.sin_addr).c_str(), ntohs(saddr.in.sin_port));

	std::string datahex;
	DataToHexString(0, 0, Memory::GetPointer(bufferPtr), len, &datahex);
	VERBOSE_LOG(SCENET, "Data Dump (%d bytes):\n%s", len, datahex.c_str());
	
	int retval;
	bool isBcast = isBroadcastIP(saddr.in.sin_addr.s_addr);
	// Broadcast/Multicast, use real broadcast/multicast if there is no one in peerlist
	if (isBcast && getActivePeerCount() > 0) {
		// Acquire Peer Lock
		peerlock.lock();
		SceNetAdhocctlPeerInfo* peer = friends;
		for (; peer != NULL; peer = peer->next) {
			// Does Skipping sending to timed out friends could cause desync when players moving group at the time MP game started?
			if (peer->last_recv == 0)
				continue;

			saddr.in.sin_addr.s_addr = peer->ip_addr;
			retval = sendto(socket, (char*)Memory::GetPointer(bufferPtr), len, flgs | MSG_NOSIGNAL, (struct sockaddr*)&saddr.addr, dstlen);
			if (retval < 0) {
				DEBUG_LOG(SCENET, "SendTo(BC): Socket error %d", errno);
			}
			else {
				DEBUG_LOG(SCENET, "SendTo(BC): Address = %s, Port = %d", ip2str(saddr.in.sin_addr).c_str(), ntohs(saddr.in.sin_port));
			}
		}
		// Free Peer Lock
		peerlock.unlock();
		retval = len;
	}
	// Unicast or real broadcast/multicast
	else {
		// FIXME: On non-Windows(including PSP too?) broadcast to INADDR_BROADCAST(255.255.255.255) might not be received by the sender itself when binded to specific IP (ie. 192.168.0.2) or INADDR_BROADCAST.
		//        Meanwhile, it might be received by itself when binded to subnet (ie. 192.168.0.255) or INADDR_ANY(0.0.0.0).
		/*if (isBcast) {
			// TODO: Replace Broadcast with Multicast to be more consistent across platform
			// Replace Limited Broadcast(255.255.255.255) with Direct Broadcast(ie. 192.168.0.255) for accurate targetting when there are multiple interfaces, to avoid receiving it's own broadcasted data through IP 169.254.x.x on Windows (which is not recognized as it's own IP by the game)
			// Get Local IP Address
			sockaddr_in sockAddr{};
			getLocalIp(&sockAddr);
			// Change the last number to 255 to indicate a common broadcast address (the accurate way should be: ip | (~subnetmask))
			((u8*)&sockAddr.sin_addr.s_addr)[3] = 255;
			saddr.in.sin_addr.s_addr = sockAddr.sin_addr.s_addr;
			DEBUG_LOG(SCENET, "SendTo(BC): Address Replacement = %s", ip2str(saddr.in.sin_addr).c_str());
		}*/
		retval = sendto(socket, (char*)Memory::GetPointer(bufferPtr), len, flgs | MSG_NOSIGNAL, (struct sockaddr*)&saddr.addr, dstlen);
	}
	if (retval < 0) {
		inetLastErrno = errno;
		if (inetLastErrno == EAGAIN)
			hleLogDebug(SCENET, retval, "errno = %d", inetLastErrno);
		else
			hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
		return retval;
	}

	return hleLogSuccessInfoI(SCENET, retval);
}

// Similar to POSIX's sendmsg or Winsock2's WSASendMsg? Are their packets compatible one another?
// Games using this: The Warrior's Code
static int sceNetInetSendmsg(int socket, u32 msghdrPtr, int flags) {
	DEBUG_LOG(SCENET, "UNTESTED %s(%i, %08x, %08x) at %08x", __FUNCTION__, socket, msghdrPtr, flags, currentMIPS->pc);
	DEBUG_LOG_REPORT_ONCE(sceNetInetSendmsg, SCENET, "UNTESTED %s(%i, %08x, %08x) at %08x", __FUNCTION__, socket, msghdrPtr, flags, currentMIPS->pc);
	// Note: sendmsg is concatenating iovec buffers before sending it, and send/sendto is just a wrapper for sendmsg according to https://stackoverflow.com/questions/4258834/how-sendmsg-works
	int retval = -1;
	if (!Memory::IsValidAddress(msghdrPtr)) {
		inetLastErrno = EFAULT;
		return hleLogError(SCENET, retval);
	}
	InetMsghdr* pspMsghdr = (InetMsghdr*)Memory::GetPointer(msghdrPtr);
	int flgs = flags & ~PSP_NET_INET_MSG_DONTWAIT; // removing non-POSIX flag, which is an alternative way to use non-blocking mode
	flgs = convertMSGFlagsPSP2Host(flgs);
	SockAddrIN4 saddr{};
#if defined(_WIN32)
	WSAMSG hdr;
	WSACMSGHDR* chdr = NULL;
	size_t iovecsize = sizeof(WSABUF);
	WSABUF* iov = (WSABUF*)malloc(pspMsghdr->msg_iovlen * iovecsize);
#else
	msghdr hdr;
	cmsghdr* chdr = nullptr;
	size_t iovecsize = sizeof(iovec);
	iovec* iov = (iovec*)malloc(pspMsghdr->msg_iovlen * iovecsize);
#endif
	if (iov == NULL) {
		inetLastErrno = ENOBUFS;
		return hleLogError(SCENET, retval);
	}
	memset(iov, 0, pspMsghdr->msg_iovlen * iovecsize);
	memset(&hdr, 0, sizeof(hdr));
	if (pspMsghdr->msg_name != 0) {
		SceNetInetSockaddr* pspSaddr = (SceNetInetSockaddr*)Memory::GetPointer(pspMsghdr->msg_name);
		saddr.addr.sa_family = pspSaddr->sa_family;
		size_t datalen = std::min(pspMsghdr->msg_namelen-(sizeof(pspSaddr->sa_len)+sizeof(pspSaddr->sa_family)), sizeof(saddr.addr.sa_data));
		memcpy(saddr.addr.sa_data, pspSaddr->sa_data, datalen);
		DEBUG_LOG(SCENET, "SendMsg: Address = %s, Port = %d", ip2str(saddr.in.sin_addr).c_str(), ntohs(saddr.in.sin_port));
#if defined(_WIN32)
		hdr.name = &saddr.addr;
		hdr.namelen = static_cast<int>(datalen+sizeof(saddr.addr.sa_family));
#else
        hdr.msg_name = &saddr.addr;
        hdr.msg_namelen = static_cast<int>(datalen+sizeof(saddr.addr.sa_family));
#endif
	}
#if defined(_WIN32)
	hdr.lpBuffers = iov;
	hdr.dwBufferCount = pspMsghdr->msg_iovlen;
#else
    hdr.msg_iov = iov;
    hdr.msg_iovlen = pspMsghdr->msg_iovlen;
#endif
	if (pspMsghdr->msg_iov != 0) {
		SceNetIovec* pspIov = (SceNetIovec*)Memory::GetPointer(pspMsghdr->msg_iov);
		for (int i = 0; i < pspMsghdr->msg_iovlen; i++) {
			if (pspIov[i].iov_base != 0) {
#if defined(_WIN32)
				iov[i].buf = (char*)Memory::GetPointer(pspIov[i].iov_base);
				iov[i].len = pspIov[i].iov_len;
#else
                iov[i].iov_base = (char*)Memory::GetPointer(pspIov[i].iov_base);
                iov[i].iov_len = pspIov[i].iov_len;
#endif
			}
		}
	}
	// Control's Level (ie. host's SOL_SOCKET to/from psp's PSP_NET_INET_SOL_SOCKET) and Type (ie. SCM_RIGHTS) might need to be converted to be cross-platform
	if (pspMsghdr->msg_control != 0) {
#if defined(_WIN32)
		chdr = (WSACMSGHDR*)malloc(pspMsghdr->msg_controllen);
#else
		chdr = (cmsghdr*)malloc(pspMsghdr->msg_controllen);
#endif
		if (chdr == NULL) {
			inetLastErrno = ENOBUFS;
			free(iov);
			return hleLogError(SCENET, retval);
		}
		InetCmsghdr* pspCmsghdr = (InetCmsghdr*)Memory::GetPointer(pspMsghdr->msg_control);
		// TODO: Convert InetCmsghdr into platform-specific struct as they're affected by 32/64bit
		memcpy(chdr, pspCmsghdr, pspMsghdr->msg_controllen);
#if defined(_WIN32)
		hdr.Control.buf = (char*)chdr; // (char*)pspCmsghdr;
		hdr.Control.len = pspMsghdr->msg_controllen;
		// Note: Many existing implementations of CMSG_FIRSTHDR never look at msg_controllen and just return the value of cmsg_control.
		if (pspMsghdr->msg_controllen >= sizeof(InetCmsghdr)) {
			// TODO: Creates our own CMSG_* macros (32-bit version of it, similar to the one on PSP) to avoid alignment/size issue that can lead to memory corruption/out of bound issue.
			for (WSACMSGHDR* cmsgptr = CMSG_FIRSTHDR(&hdr); cmsgptr != NULL; cmsgptr = CMSG_NXTHDR(&hdr, cmsgptr)) {
				cmsgptr->cmsg_type = convertCMsgTypePSP2Host(cmsgptr->cmsg_type, cmsgptr->cmsg_level);
				cmsgptr->cmsg_level = convertSockoptLevelPSP2Host(cmsgptr->cmsg_level);
			}
		}
#else
		hdr.msg_control = (char*)chdr; // (char*)pspCmsghdr;
		hdr.msg_controllen = pspMsghdr->msg_controllen;
		// Note: Many existing implementations of CMSG_FIRSTHDR never look at msg_controllen and just return the value of cmsg_control.
		if (pspMsghdr->msg_controllen >= sizeof(InetCmsghdr)) {
			for (cmsghdr* cmsgptr = CMSG_FIRSTHDR(&hdr); cmsgptr != NULL; cmsgptr = CMSG_NXTHDR(&hdr, cmsgptr)) {
				cmsgptr->cmsg_type = convertCMsgTypePSP2Host(cmsgptr->cmsg_type, cmsgptr->cmsg_level);
				cmsgptr->cmsg_level = convertSockoptLevelPSP2Host(cmsgptr->cmsg_level);
			}
		}
#endif
	}
	// Flags (ie. PSP_NET_INET_MSG_OOB) might need to be converted to be cross-platform
#if defined(_WIN32)
	hdr.dwFlags = convertMSGFlagsPSP2Host(pspMsghdr->msg_flags & ~PSP_NET_INET_MSG_DONTWAIT) | MSG_NOSIGNAL;
#else
    hdr.msg_flags = convertMSGFlagsPSP2Host(pspMsghdr->msg_flags & ~PSP_NET_INET_MSG_DONTWAIT) | MSG_NOSIGNAL;
#endif
	unsigned long sent = 0;
	bool isBcast = isBroadcastIP(saddr.in.sin_addr.s_addr);
	// Broadcast/Multicast, use real broadcast/multicast if there is no one in peerlist
	if (isBcast && getActivePeerCount() > 0) {
		// Acquire Peer Lock
		peerlock.lock();
		SceNetAdhocctlPeerInfo* peer = friends;
		for (; peer != NULL; peer = peer->next) {
			// Does Skipping sending to timed out friends could cause desync when players moving group at the time MP game started?
			if (peer->last_recv == 0)
				continue;

			saddr.in.sin_addr.s_addr = peer->ip_addr;
#if defined(_WIN32)
			int result = WSASendMsg(socket, &hdr, flgs | MSG_NOSIGNAL, &sent, NULL, NULL);
			if (static_cast<int>(sent) > retval)
				retval = sent;
#else
			size_t result = sendmsg(socket, &hdr, flgs | MSG_NOSIGNAL);
			if (static_cast<int>(result) > retval)
				retval = result;
#endif
			if (retval != SOCKET_ERROR) {
				DEBUG_LOG(SCENET, "SendMsg(BC): Address = %s, Port = %d", ip2str(saddr.in.sin_addr).c_str(), ntohs(saddr.in.sin_port));
			}
			else {
				DEBUG_LOG(SCENET, "SendMsg(BC): Socket error %d", errno);
			}
		}
		// Free Peer Lock
		peerlock.unlock();
		// TODO: Calculate number of bytes supposed to be sent
		retval = std::max(retval, 0); // Broadcast always success?
	}
	// Unicast or real broadcast/multicast
	else {
		// FIXME: On non-Windows(including PSP too?) broadcast to INADDR_BROADCAST(255.255.255.255) might not be received by the sender itself when binded to specific IP (ie. 192.168.0.2) or INADDR_BROADCAST.
		//        Meanwhile, it might be received by itself when binded to subnet (ie. 192.168.0.255) or INADDR_ANY(0.0.0.0).
		/*if (isBcast) {
			// TODO: Replace Broadcast with Multicast to be more consistent across platform
			// Replace Limited Broadcast(255.255.255.255) with Direct Broadcast(ie. 192.168.0.255) for accurate targetting when there are multiple interfaces, to avoid receiving it's own broadcasted data through IP 169.254.x.x on Windows (which is not recognized as it's own IP by the game)
			// Get Local IP Address
			sockaddr_in sockAddr{};
			getLocalIp(&sockAddr);
			// Change the last number to 255 to indicate a common broadcast address (the accurate way should be: ip | (~subnetmask))
			((u8*)&sockAddr.sin_addr.s_addr)[3] = 255;
			saddr.in.sin_addr.s_addr = sockAddr.sin_addr.s_addr;
			DEBUG_LOG(SCENET, "SendMsg(BC): Address Replacement = %s", ip2str(saddr.in.sin_addr).c_str());
		}*/
#if defined(_WIN32)
		int result = WSASendMsg(socket, &hdr, flgs | MSG_NOSIGNAL, &sent, NULL, NULL);
		if (result != SOCKET_ERROR)
			retval = sent;
#else
		retval = sendmsg(socket, &hdr, flgs | MSG_NOSIGNAL);
#endif
	}
	free(chdr);
	free(iov);
/*  // Example with 1 Msg buffer and without CMsg
	msghdr msg;
	iovec iov[1]; 
	int buflen = pspMsghdr->msg_iovlen;
	char* buf = (char*)malloc(buflen);

	memset(&msg, 0, sizeof(msg));
	msg.msg_iov = iov;
	msg.msg_iovlen = 1;
	iov[0].iov_base = buf;
	iov[0].iov_len = buflen;

	retval = sendmsg(socket, &msg, flags);
	free(buf);
*/
	if (retval < 0) {
		inetLastErrno = errno;
		if (inetLastErrno == EAGAIN)
			hleLogDebug(SCENET, retval, "errno = %d", inetLastErrno);
		else
			hleLogError(SCENET, retval, "errno = %d", inetLastErrno);
		return retval;
	}
	return hleLogSuccessInfoI(SCENET, retval); // returns number of bytes sent?
}

// Similar to POSIX's recvmsg or Mswsock's WSARecvMsg? Are their packets compatible one another?
// Games using this: World of Poker
static int sceNetInetRecvmsg(int socket, u32 msghdrPtr, int flags) {
	ERROR_LOG(SCENET, "UNIMPL %s(%i, %08x, %08x) at %08x", __FUNCTION__, socket, msghdrPtr, flags, currentMIPS->pc);
	DEBUG_LOG_REPORT_ONCE(sceNetInetRecvmsg, SCENET, "UNIMPL %s(%i, %08x, %08x) at %08x", __FUNCTION__, socket, msghdrPtr, flags, currentMIPS->pc);
	// Reference: http://www.masterraghu.com/subjects/np/introduction/unix_network_programming_v1.3/ch14lev1sec5.html
	int retval = -1;
	if (!Memory::IsValidAddress(msghdrPtr)) {
		inetLastErrno = EFAULT;
		return hleLogError(SCENET, retval);
	}
	InetMsghdr* pspMsghdr = (InetMsghdr*)Memory::GetPointer(msghdrPtr);
	int flgs = flags & ~PSP_NET_INET_MSG_DONTWAIT; // removing non-POSIX flag, which is an alternative way to use non-blocking mode
	flgs = convertMSGFlagsPSP2Host(flgs);
	SockAddrIN4 saddr{};
#if defined(_WIN32)
	WSAMSG hdr;
	WSACMSGHDR* chdr = NULL;
	size_t iovecsize = sizeof(WSABUF);
	WSABUF* iov = (WSABUF*)malloc(pspMsghdr->msg_iovlen * iovecsize);
#else
	msghdr hdr;
	cmsghdr* chdr = nullptr;
	size_t iovecsize = sizeof(iovec);
	iovec* iov = (iovec*)malloc(pspMsghdr->msg_iovlen * iovecsize);
#endif
	if (iov == NULL) {
		inetLastErrno = ENOBUFS;
		return hleLogError(SCENET, retval);
	}
	memset(iov, 0, pspMsghdr->msg_iovlen * iovecsize);
	memset(&hdr, 0, sizeof(hdr));
	// TODO: Do similar to the already working sceNetInetSendmsg but in reverse
	//if (pspMsghdr->msg_name != 0) { ... }


	return hleLogError(SCENET, retval); // returns number of bytes received?
}

int sceNetApctlConnect(int confId) {
	WARN_LOG(SCENET, "UNTESTED %s(%i)", __FUNCTION__, confId);
	if (!g_Config.bEnableWlan) 
		return hleLogError(SCENET, ERROR_NET_APCTL_WLAN_SWITCH_OFF, "apctl wlan off");

	if (netApctlState != PSP_NET_APCTL_STATE_DISCONNECTED)
		return hleLogError(SCENET, ERROR_NET_APCTL_NOT_DISCONNECTED, "apctl not disconnected");

	// Is this confId is the index to the scanning's result data or sceNetApctlGetBSSDescIDListUser result?
	netApctlInfoId = confId;
	// Note: We're borrowing AdhocServer for Grouping purpose, so we can simulate Broadcast over the internet just like Adhoc's pro-online implementation
	int ret = sceNetAdhocctlConnect("INFRA");

	if (netApctlState == PSP_NET_APCTL_STATE_DISCONNECTED)
		__UpdateApctlHandlers(0, PSP_NET_APCTL_STATE_JOINING, PSP_NET_APCTL_EVENT_CONNECT_REQUEST, 0);
	//hleDelayResult(0, "give time to init/cleanup", adhocEventDelayMS * 1000);
	// TODO: Blocks current thread and wait for a state change to prevent user-triggered connection attempt from causing events to piles up
	return hleLogDebug(SCENET, 0, "connect = %i", ret);
}

int sceNetApctlDisconnect() {
	WARN_LOG(SCENET, "UNTESTED %s()", __FUNCTION__);
	// Like its 'sister' function sceNetAdhocctlDisconnect, we need to alert Apctl handlers that a disconnect took place
	// or else games like Phantasy Star Portable 2 will hang at certain points (e.g. returning to the main menu after trying to connect to PSN).
	// Note: Since we're borrowing AdhocServer for Grouping purpose, we should disconnect too
	sceNetAdhocctlDisconnect();

	// Discards any pending events so we can disconnect immediately
	apctlEvents.clear();
	__UpdateApctlHandlers(netApctlState, PSP_NET_APCTL_STATE_DISCONNECTED, PSP_NET_APCTL_EVENT_DISCONNECT_REQUEST, 0);
	// TODO: Blocks current thread and wait for a state change, but the state should probably need to be changed within 1 frame-time (~16ms) 
	return 0;
}

int NetApctl_GetState() {
	return netApctlState;
}

static int sceNetApctlGetState(u32 pStateAddr) {
	//if (!netApctlInited) return hleLogError(SCENET, ERROR_NET_APCTL_NOT_IN_BSS, "apctl not in bss");

	// Valid Arguments
	if (Memory::IsValidAddress(pStateAddr)) {
		// Return Thread Status
		Memory::Write_U32(NetApctl_GetState(), pStateAddr);
		// Return Success
		return hleLogSuccessI(SCENET, 0);
	}

	return hleLogError(SCENET, -1, "apctl invalid arg"); // 0x8002013A or ERROR_NET_WLAN_INVALID_ARG ?
}

int NetApctl_ScanUser() {
	if (!g_Config.bEnableWlan) 
		return hleLogError(SCENET, ERROR_NET_APCTL_WLAN_SWITCH_OFF, "apctl wlan off");

	// Scan probably only works when not in connected state, right?
	if (netApctlState != PSP_NET_APCTL_STATE_DISCONNECTED)
		return hleLogError(SCENET, ERROR_NET_APCTL_NOT_DISCONNECTED, "apctl not disconnected");

	__UpdateApctlHandlers(0, PSP_NET_APCTL_STATE_SCANNING, PSP_NET_APCTL_EVENT_SCAN_REQUEST, 0);
	// TODO: Blocks current thread and wait for a state change to prevent user-triggered scan attempt from causing events to piles up
	return 0;
}

static int sceNetApctlScanUser() {
	ERROR_LOG(SCENET, "UNIMPL %s()", __FUNCTION__);
	return NetApctl_ScanUser();
}

int NetApctl_GetBSSDescIDListUser(u32 sizeAddr, u32 bufAddr) {
	const int userInfoSize = 8; // 8 bytes per entry (next address + entry id)
	// Faking 4 entries, games like MGS:PW Recruit will need to have a different AP for each entry
	int entries = 4;
	if (!Memory::IsValidAddress(sizeAddr) || !Memory::IsValidAddress(bufAddr))
		return hleLogError(SCENET, -1, "apctl invalid arg"); // 0x8002013A or ERROR_NET_WLAN_INVALID_ARG ?

	int size = Memory::Read_U32(sizeAddr);
	// Return size required
	Memory::Write_U32(entries * userInfoSize, sizeAddr);

	if (bufAddr != 0 && Memory::IsValidAddress(sizeAddr)) {
		int offset = 0;
		for (int i = 0; i < entries; i++) {
			// Check if enough space available to write the next structure
			if (offset + userInfoSize > size) {
				break;
			}

			DEBUG_LOG(SCENET, "%s writing ID#%d to %08x", __FUNCTION__, i, bufAddr + offset);

			// Pointer to next Network structure in list
			Memory::Write_U32((i + 1) * userInfoSize + bufAddr, bufAddr + offset);
			offset += 4;

			// Entry ID
			Memory::Write_U32(i, bufAddr + offset);
			offset += 4;
		}
		// Fix the last Pointer
		if (offset > 0)
			Memory::Write_U32(0, bufAddr + offset - userInfoSize);
	}

	return 0;
}

static int sceNetApctlGetBSSDescIDListUser(u32 sizeAddr, u32 bufAddr) {
	WARN_LOG(SCENET, "UNTESTED %s(%08x, %08x)", __FUNCTION__, sizeAddr, bufAddr);
	return NetApctl_GetBSSDescIDListUser(sizeAddr, bufAddr);
}

int NetApctl_GetBSSDescEntryUser(int entryId, int infoId, u32 resultAddr) {
	if (!Memory::IsValidAddress(resultAddr))
		return hleLogError(SCENET, -1, "apctl invalid arg"); // 0x8002013A or ERROR_NET_WLAN_INVALID_ARG ?

	// Generate an SSID name
	char dummySSID[APCTL_SSID_MAXLEN] = "WifiAP0";
	dummySSID[6] += static_cast<char>(entryId);

	switch (infoId) {
	case PSP_NET_APCTL_DESC_IBSS: // IBSS, 6 bytes
		if (entryId == 0)
			Memory::Memcpy(resultAddr, netApctlInfo.bssid, sizeof(netApctlInfo.bssid), "GetBSSDescEntryUser");
		else {
			// Generate a BSSID/MAC address
			char dummyMAC[ETHER_ADDR_LEN];
			memset(dummyMAC, entryId, sizeof(dummyMAC));
			// Making sure the 1st 2-bits on the 1st byte of OUI are zero to prevent issue with some games (ie. Gran Turismo)
			dummyMAC[0] &= 0xfc;
			Memory::Memcpy(resultAddr, dummyMAC, sizeof(dummyMAC), "GetBSSDescEntryUser");
		}
		break;
	case PSP_NET_APCTL_DESC_SSID_NAME:
		// Return 32 bytes
		if (entryId == 0)
			Memory::Memcpy(resultAddr, netApctlInfo.ssid, sizeof(netApctlInfo.ssid), "GetBSSDescEntryUser");
		else {
			Memory::Memcpy(resultAddr, dummySSID, sizeof(dummySSID), "GetBSSDescEntryUser");
		}
		break;
	case PSP_NET_APCTL_DESC_SSID_NAME_LENGTH:
		// Return one 32-bit value
		if (entryId == 0)
			Memory::Write_U32(netApctlInfo.ssidLength, resultAddr);
		else {
			// Calculate the SSID length
			Memory::Write_U32((u32)strlen(dummySSID), resultAddr);
		}
		break;
	case PSP_NET_APCTL_DESC_CHANNEL:
		// FIXME: Return one 1 byte value or may be 32-bit if this is not a channel?
		if (entryId == 0)
			Memory::Write_U8(netApctlInfo.channel, resultAddr);
		else {
			// Generate channel for testing purposes, not even sure whether this is channel or not, MGS:PW seems to treat the data as u8
			Memory::Write_U8(entryId, resultAddr);
		}
		break;
	case PSP_NET_APCTL_DESC_SIGNAL_STRENGTH:
		// Return 1 byte
		if (entryId == 0)
			Memory::Write_U8(netApctlInfo.strength, resultAddr);
		else {
			// Randomize signal strength between 1%~99% since games like MGS:PW are using signal strength to determine the strength of the recruit
			Memory::Write_U8((int)(((float)rand() / (float)RAND_MAX) * 99.0 + 1.0), resultAddr);
		}
		break;
	case PSP_NET_APCTL_DESC_SECURITY:
		// Return one 32-bit value
		Memory::Write_U32(netApctlInfo.securityType, resultAddr);
		break;
	default:
		return hleLogError(SCENET, ERROR_NET_APCTL_INVALID_CODE, "unknown info id");
	}

	return 0;
}

static int sceNetApctlGetBSSDescEntryUser(int entryId, int infoId, u32 resultAddr) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %i, %08x)", __FUNCTION__, entryId, infoId, resultAddr);
	return NetApctl_GetBSSDescEntryUser(entryId, infoId, resultAddr);
}

static int sceNetApctlScanSSID2() {
	WARN_LOG(SCENET, "UNTESTED %s() at %08x", __FUNCTION__, currentMIPS->pc);
	return NetApctl_ScanUser();
}

/**************
* Arg1 = output buffer size being filled? (initially the same with Arg3 ?)
* Arg2 = output buffer? (linked list where the 1st 32-bit is the next address? followed by entry Id? ie. 8-bytes per entry?)
* Arg3 = max buffer size? (ie. 0x100 ?)
* Arg4 = input flag? (initially 0/1 ?)
***************/
static int sceNetApctlGetBSSDescIDList2(u32 Arg1, u32 Arg2, u32 Arg3, u32 Arg4) {
	WARN_LOG(SCENET, "UNTESTED %s(%08x, %08x, %08x, %08x) at %08x", __FUNCTION__, Arg1, Arg2, Arg3, Arg4, currentMIPS->pc);
	return NetApctl_GetBSSDescIDListUser(Arg1, Arg2);
}

/**************
* Arg1 = a value returned from sceNetApctlGetBSSDescIDList2 ? entryId?
* Arg2 = input field type within the entry desc (ie. PSP_NET_APCTL_DESC_SSID_NAME ?)
* Arg3 = output buffer for retrieved entry data? (max size = 32 bytes? ie. APCTL_SSID_MAXLEN ? or similar to SceNetApctlInfoInternal union ?)
***************/
static int sceNetApctlGetBSSDescEntry2(int entryId, int infoId, u32 resultAddr) {
	WARN_LOG(SCENET, "UNTESTED %s(%i, %i, %08x) at %08x", __FUNCTION__, entryId, infoId, resultAddr, currentMIPS->pc);
	return NetApctl_GetBSSDescEntryUser(entryId, infoId, resultAddr);
}

static int sceNetResolverInit()
{
	ERROR_LOG(SCENET, "UNIMPL %s()", __FUNCTION__);
	return 0;
}

static int sceNetResolverTerm()
{
	ERROR_LOG(SCENET, "UNIMPL %s()", __FUNCTION__);
	netResolvers.clear(); // Let's not leaks! JPCSP doesn't clear or removes created resolvers on Term, may be because it uses SceUID ?
	return 0;
}

// Note: timeouts are in seconds
int NetResolver_StartNtoA(int rid, u32 hostnamePtr, u32 inAddrPtr, int timeout, int retry)
{
	if (netResolvers.find(rid) == netResolvers.end())
		return hleLogError(SCENET, ERROR_NET_RESOLVER_BAD_ID, "Bad Resolver Id: %i", rid);

	auto& resolver = netResolvers[rid];
	addrinfo* resolved = nullptr;
	std::string err, hostname = std::string(safe_string(Memory::GetCharPointer(hostnamePtr)));
	SockAddrIN4 addr{};
	addr.in.sin_addr.s_addr = INADDR_NONE;
	// TODO: Use a lightweight DNS Resolver library (https://github.com/wahern/dns or https://github.com/CesiumComputer/sldr or https://github.com/b17v134/dns may be), 
	//       So we can support Custom DNS Server without users messing around with Network adapter settings.
	//       Also need to implement built-in hosts file to avoid users from changing system hosts file which requires admin/sudo (for users with enforced DNS server by their ISP, thus unable to use custom DNS server).
	// TODO: Resolves using Primary DNS (& Secondary DNS) Server set on Apctl.
	// FIXME: Should probably do this on a background thread, at least for the Async version
	resolver.isRunning = true;
	if (!net::DNSResolve(hostname, "", &resolved, err)) {
		// TODO: Return an error based on the outputted "err" (unfortunately it's already converted to string)
		return hleLogError(SCENET, ERROR_NET_RESOLVER_INVALID_HOST, "DNS Error Resolving %s (%s)\n", hostname.c_str(), err.c_str());
	}
	if (resolved) {
		for (auto ptr = resolved; ptr != NULL; ptr = ptr->ai_next) {
			switch (ptr->ai_family) {
			case AF_INET:
				addr.in = *(sockaddr_in*)ptr->ai_addr;
				break;
			}
		}
		net::DNSResolveFree(resolved);

		Memory::Write_U32(addr.in.sin_addr.s_addr, inAddrPtr);
		INFO_LOG(SCENET, "%s - Hostname: %s => IPv4: %s", __FUNCTION__, hostname.c_str(), ip2str(addr.in.sin_addr, false).c_str());
	}
	resolver.isRunning = false;

	return 0;
}

static int sceNetResolverStartNtoA(int rid, u32 hostnamePtr, u32 inAddrPtr, int timeout, int retry)
{
	WARN_LOG(SCENET, "UNTESTED %s(%d, %08x, %08x, %d, %d) at %08x", __FUNCTION__, rid, hostnamePtr, inAddrPtr, timeout, retry, currentMIPS->pc);
	return NetResolver_StartNtoA(rid, hostnamePtr, inAddrPtr, timeout, retry);
}

static int sceNetResolverStartNtoAAsync(int rid, u32 hostnamePtr, u32 inAddrPtr, int timeout, int retry)
{
	ERROR_LOG_REPORT_ONCE(sceNetResolverStartNtoAAsync, SCENET, "UNIMPL %s(%d, %08x, %08x, %d, %d) at %08x", __FUNCTION__, rid, hostnamePtr, inAddrPtr, timeout, retry, currentMIPS->pc);
	return NetResolver_StartNtoA(rid, hostnamePtr, inAddrPtr, timeout, retry);
}

// FIXME: May be used to get the resolver.isRunning of one or more resolver(s)?
static int sceNetResolverPollAsync(int rid, u32 unknown)
{
	ERROR_LOG_REPORT_ONCE(sceNetResolverPollAsync, SCENET, "UNIMPL %s(%d, %08x) at %08x", __FUNCTION__, rid, unknown, currentMIPS->pc);
	return 0;
}

// FIXME: May be used to block current thread until resolver.isRunning = false?
static int sceNetResolverWaitAsync(int rid, u32 unknown)
{
	ERROR_LOG_REPORT_ONCE(sceNetResolverWaitAsync, SCENET, "UNIMPL %s(%d, %08x) at %08x", __FUNCTION__, rid, unknown, currentMIPS->pc);
	return 0;
}

// FIXME: Something like [the deprecated] gethostbyname may be?
static int sceNetResolverStartAtoN(int rid, u32 inAddr, u32 hostnamePtr, int hostnameLength, int timeout, int retry)
{
	ERROR_LOG_REPORT_ONCE(sceNetResolverStartAtoN, SCENET, "UNIMPL %s(%d, %08x[%s], %08x, %i, %i, %i) at %08x", __FUNCTION__, rid, inAddr, ip2str(*(in_addr*)&inAddr, false).c_str(), hostnamePtr, hostnameLength, timeout, retry, currentMIPS->pc);
	return 0;
}

static int sceNetResolverStartAtoNAsync(int rid, u32 inAddr, u32 hostnamePtr, int hostnameLength, int timeout, int retry)
{
	ERROR_LOG_REPORT_ONCE(sceNetResolverStartAtoNAsync, SCENET, "UNIMPL %s(%d, %08x[%s], %08x, %i, %i, %i) at %08x", __FUNCTION__, rid, inAddr, ip2str(*(in_addr*)&inAddr, false).c_str(), hostnamePtr, hostnameLength, timeout, retry, currentMIPS->pc);
	return 0;
}

// FIXME: What to do with the [temporary] buffer Args? as input or output? is it mandatory or optional?
static int sceNetResolverCreate(u32 ridPtr, u32 bufferPtr, int bufferLen)
{
	WARN_LOG(SCENET, "UNTESTED %s(%08x[%d], %08x, %d) at %08x", __FUNCTION__, ridPtr, Memory::Read_U32(ridPtr), bufferPtr, bufferLen, currentMIPS->pc);
	if (!Memory::IsValidRange(ridPtr, 4))
		return hleLogError(SCENET, ERROR_NET_RESOLVER_INVALID_PTR, "Invalid Ptr: %08x", ridPtr);

	if (Memory::IsValidRange(bufferPtr, 4) && bufferLen < 1)
		return hleLogError(SCENET, ERROR_NET_RESOLVER_INVALID_BUFLEN, "Invalid Buffer Length: %i", bufferLen);

	// Note: JPCSP uses SceUidManager to generate the id
	NetResolver resolver = { 0 };
	int rid = 1; // FIXME: Is this id starts from 1 (as most id) ? There should be MAX_RESOLVERS_ID too (may be 32 ?) as there is ERROR_NET_RESOLVER_ID_MAX error
	while (netResolvers.find(rid) != netResolvers.end())
		++rid;

	// TODO: Need to confirm the isRunning status right after creation, JPCSP seems to set the value to true on Create instead of on Start
	resolver.id = rid;
	resolver.bufferAddr = bufferPtr;
	resolver.bufferLen = bufferLen;
	netResolvers[rid] = resolver;

	Memory::Write_U32(rid, ridPtr);
	return 0;
}

static int sceNetResolverStop(int rid)
{
	WARN_LOG(SCENET, "UNTESTED %s(%d) at %08x", __FUNCTION__, rid, currentMIPS->pc);
	if (netResolvers.find(rid) == netResolvers.end())
		return hleLogError(SCENET, ERROR_NET_RESOLVER_BAD_ID, "Bad Resolver Id: %i", rid);

	auto& resolver = netResolvers[rid];
	if (!resolver.isRunning)
		return hleLogError(SCENET, ERROR_NET_RESOLVER_ALREADY_STOPPED, "Resolver Already Stopped (Id: %i)", rid);

	resolver.isRunning = false;
	return 0;
}

static int sceNetResolverDelete(int rid)
{
	WARN_LOG(SCENET, "UNTESTED %s(%d) at %08x", __FUNCTION__, rid, currentMIPS->pc);
	if (netResolvers.find(rid) == netResolvers.end())
		return hleLogError(SCENET, ERROR_NET_RESOLVER_BAD_ID, "Bad Resolver Id: %i", rid);

	netResolvers.erase(rid);
	return 0;
}

static int sceNetApctlAddInternalHandler(u32 handlerPtr, u32 handlerArg) {
	ERROR_LOG(SCENET, "UNIMPL %s(%08x, %08x)", __FUNCTION__, handlerPtr, handlerArg);
	// This seems to be a 2nd kind of handler
	return NetApctl_AddHandler(handlerPtr, handlerArg);
}

static int sceNetApctlDelInternalHandler(u32 handlerID) {
	ERROR_LOG(SCENET, "UNIMPL %s(%i)", __FUNCTION__, handlerID);
	// This seems to be a 2nd kind of handler
	return NetApctl_DelHandler(handlerID);
}

static int sceNetApctl_A7BB73DF(u32 handlerPtr, u32 handlerArg) {
	ERROR_LOG(SCENET, "UNIMPL %s(%08x, %08x)", __FUNCTION__, handlerPtr, handlerArg);
	// This seems to be a 3rd kind of handler
	return sceNetApctlAddHandler(handlerPtr, handlerArg);
}

static int sceNetApctl_6F5D2981(u32 handlerID) {
	ERROR_LOG(SCENET, "UNIMPL %s(%i)", __FUNCTION__, handlerID);
	// This seems to be a 3rd kind of handler
	return sceNetApctlDelHandler(handlerID);
}

static int sceNetApctl_lib2_69745F0A(int handlerId) {
	return hleLogError(SCENET, 0, "unimplemented");
}

static int sceNetApctl_lib2_4C19731F(int code, u32 pInfoAddr) {
	ERROR_LOG(SCENET, "UNIMPL %s(%i, %08x)", __FUNCTION__, code, pInfoAddr);
	return sceNetApctlGetInfo(code, pInfoAddr);
}

static int sceNetApctlScan() {
	ERROR_LOG(SCENET, "UNIMPL %s()", __FUNCTION__);
	return NetApctl_ScanUser();
}

static int sceNetApctlGetBSSDescIDList(u32 sizeAddr, u32 bufAddr) {
	ERROR_LOG(SCENET, "UNIMPL %s(%08x, %08x)", __FUNCTION__, sizeAddr, bufAddr);
	return sceNetApctlGetBSSDescIDListUser(sizeAddr, bufAddr);
}

static int sceNetApctlGetBSSDescEntry(int entryId, int infoId, u32 resultAddr) {
	ERROR_LOG(SCENET, "UNIMPL %s(%i, %i, %08x)", __FUNCTION__, entryId, infoId, resultAddr);
	return sceNetApctlGetBSSDescEntryUser(entryId, infoId, resultAddr);
}

static int sceNetApctl_lib2_C20A144C(int connIndex, u32 ps3MacAddressPtr) {
	ERROR_LOG(SCENET, "UNIMPL %s(%i, %08x)", __FUNCTION__, connIndex, ps3MacAddressPtr);
	return sceNetApctlConnect(connIndex);
}

// unknown1 = source port for sending SSDP packet? unknown2 = discovery timeout?
static int sceNetUpnpInit(int unknown1,int unknown2)
{
	ERROR_LOG_REPORT_ONCE(sceNetUpnpInit, SCENET, "UNIMPL sceNetUpnpInit(%d, %d)", unknown1, unknown2);	
	return 0;
}

static int sceNetUpnpStart()
{
	ERROR_LOG(SCENET, "UNIMPL sceNetUpnpStart()");
	return 0;
}

static int sceNetUpnpStop()
{
	ERROR_LOG(SCENET, "UNIMPL sceNetUpnpStop()");
	return 0;
}

static int sceNetUpnpTerm()
{
	ERROR_LOG(SCENET, "UNIMPL sceNetUpnpTerm()");
	return 0;
}

static int sceNetUpnpGetNatInfo(u32 unkStructPtr)
{
	ERROR_LOG(SCENET, "UNIMPL sceNetUpnpGetNatInfo(%08x)", unkStructPtr);

	// Unknown struct of 16 bytes
	Memory::Memset(unkStructPtr, 0, 16);

	return 0;
}

static int sceNetUpnp_8513C6D1(u32 unk1, u32 unk2, u32 unk3)
{
	ERROR_LOG(SCENET, "UNIMPL sceNetUpnp_8513C6D1(%08x, %08x, %08x)", unk1, unk2, unk3);
	return 0;
}

static int sceNetUpnp_FDA78483()
{
	ERROR_LOG(SCENET, "UNIMPL sceNetUpnp_FDA78483()");
	return 0;
}

static int sceNetUpnp_1038E77A(u32 unkStructPtr)
{
	ERROR_LOG(SCENET, "UNIMPL sceNetUpnp_1038E77A(%08x)", unkStructPtr);

	// Unknown struct of 48 bytes
	Memory::Memset(unkStructPtr, 0, 48);
	Memory::Write_U32(1, unkStructPtr + 4);

	return 0;
}

static int sceNetGetDropRate(u32 dropRateAddr, u32 dropDurationAddr)
{
	Memory::Write_U32(netDropRate, dropRateAddr);
	Memory::Write_U32(netDropDuration, dropDurationAddr);
	return hleLogSuccessInfoI(SCENET, 0);
}

static int sceNetSetDropRate(u32 dropRate, u32 dropDuration)
{
	netDropRate = dropRate;
	netDropDuration = dropDuration;
	return hleLogSuccessInfoI(SCENET, 0);
}

const HLEFunction sceNet[] = {
	{0X39AF39A6, &WrapI_UUUUU<sceNetInit>,           "sceNetInit",                      'i', "xxxxx"},
	{0X281928A9, &WrapU_V<sceNetTerm>,               "sceNetTerm",                      'x', ""     },
	{0X89360950, &WrapV_UU<sceNetEtherNtostr>,       "sceNetEtherNtostr",               'v', "xx"   },
	{0XD27961C9, &WrapV_UU<sceNetEtherStrton>,       "sceNetEtherStrton",               'v', "xx"   },
	{0X0BF0A3AE, &WrapU_U<sceNetGetLocalEtherAddr>,  "sceNetGetLocalEtherAddr",         'x', "x"    },
	{0X50647530, &WrapI_I<sceNetFreeThreadinfo>,     "sceNetFreeThreadinfo",            'i', "i"    },
	{0XCC393E48, &WrapI_U<sceNetGetMallocStat>,      "sceNetGetMallocStat",             'i', "p"    },
	{0XAD6844C6, &WrapI_I<sceNetThreadAbort>,        "sceNetThreadAbort",               'i', "i"    },
};

const HLEFunction sceNetResolver[] = {
	{0X224C5F44, &WrapI_IUUII<sceNetResolverStartNtoA>,      "sceNetResolverStartNtoA",         'i', "ixxii" },
	{0X244172AF, &WrapI_UUI<sceNetResolverCreate>,           "sceNetResolverCreate",            'i', "xxi"   },
	{0X94523E09, &WrapI_I<sceNetResolverDelete>,             "sceNetResolverDelete",            'i', "i"     },
	{0XF3370E61, &WrapI_V<sceNetResolverInit>,               "sceNetResolverInit",              'i', ""      },
	{0X808F6063, &WrapI_I<sceNetResolverStop>,               "sceNetResolverStop",              'i', "i"     },
	{0X6138194A, &WrapI_V<sceNetResolverTerm>,               "sceNetResolverTerm",              'i', ""      },
	{0X629E2FB7, &WrapI_IUUIII<sceNetResolverStartAtoN>,     "sceNetResolverStartAtoN",         'i', "ixxiii"},
	{0X14C17EF9, &WrapI_IUUII<sceNetResolverStartNtoAAsync>, "sceNetResolverStartNtoAAsync",    'i', "ixxii" },
	{0XAAC09184, &WrapI_IUUIII<sceNetResolverStartAtoNAsync>,"sceNetResolverStartAtoNAsync",    'i', "ixxiii"},
	{0X12748EB9, &WrapI_IU<sceNetResolverWaitAsync>,         "sceNetResolverWaitAsync",         'i', "ix"    },
	{0X4EE99358, &WrapI_IU<sceNetResolverPollAsync>,         "sceNetResolverPollAsync",         'i', "ix"    },
};

const HLEFunction sceNetInet[] = {
	{0X17943399, &WrapI_V<sceNetInetInit>,           "sceNetInetInit",                  'i', ""       },
	{0X4CFE4E56, &WrapI_II<sceNetInetShutdown>,      "sceNetInetShutdown",              'i', "ii"     },
	{0XA9ED66B9, &WrapI_V<sceNetInetTerm>,           "sceNetInetTerm",                  'i', ""       },
	{0X8B7B220F, &WrapI_III<sceNetInetSocket>,       "sceNetInetSocket",                'i', "iii"    },
	{0X2FE71FE7, &WrapI_IIIUI<sceNetInetSetsockopt>, "sceNetInetSetsockopt",            'i', "iiixi"  },
	{0X4A114C7C, &WrapI_IIIUU<sceNetInetGetsockopt>, "sceNetInetGetsockopt",            'i', "iiixx"  },
	{0X410B34AA, &WrapI_IUI<sceNetInetConnect>,      "sceNetInetConnect",               'i', "ixi"    },
	{0X805502DD, &WrapI_I<sceNetInetCloseWithRST>,   "sceNetInetCloseWithRST",          'i', "i"      },
	{0XD10A1A7A, &WrapI_II<sceNetInetListen>,        "sceNetInetListen",                'i', "ii"     },
	{0XDB094E1B, &WrapI_IUU<sceNetInetAccept>,       "sceNetInetAccept",                'i', "ixx"    },
	{0XFAABB1DD, &WrapI_UUI<sceNetInetPoll>,         "sceNetInetPoll",                  'i', "xxi"    },
	{0X5BE8D595, &WrapI_IUUUU<sceNetInetSelect>,     "sceNetInetSelect",                'i', "ixxxx"  },
	{0X8D7284EA, &WrapI_I<sceNetInetClose>,          "sceNetInetClose",                 'i', "i"      },
	{0XCDA85C99, &WrapI_IUUU<sceNetInetRecv>,        "sceNetInetRecv",                  'i', "ixxx"   },
	{0XC91142E4, &WrapI_IUIIUU<sceNetInetRecvfrom>,  "sceNetInetRecvfrom",              'i', "ixiixx" },
	{0XEECE61D2, &WrapI_IUI<sceNetInetRecvmsg>,      "sceNetInetRecvmsg",               'i', "ixi"    },
	{0X7AA671BC, &WrapI_IUUU<sceNetInetSend>,        "sceNetInetSend",                  'i', "ixxx"   },
	{0X05038FC7, &WrapI_IUIIUI<sceNetInetSendto>,	 "sceNetInetSendto",                'i', "ixiixi" },
	{0X774E36F4, &WrapI_IUI<sceNetInetSendmsg>,      "sceNetInetSendmsg",               'i', "ixi"    },
	{0XFBABE411, &WrapI_V<sceNetInetGetErrno>,       "sceNetInetGetErrno",              'i', ""       },
	{0X1A33F9AE, &WrapI_IUI<sceNetInetBind>,         "sceNetInetBind",                  'i', "ixi"    },
	{0XB75D5B0A, &WrapU_C<sceNetInetInetAddr>,       "sceNetInetInetAddr",              'x', "s"      },
	{0X1BDF5D13, &WrapI_CU<sceNetInetInetAton>,      "sceNetInetInetAton",              'i', "sx"     },
	{0XD0792666, &WrapU_IUUU<sceNetInetInetNtop>,    "sceNetInetInetNtop",              'x', "ixxx"   },
	{0XE30B8C19, &WrapI_ICU<sceNetInetInetPton>,     "sceNetInetInetPton",              'i', "isx"    },
	{0X8CA3A97E, &WrapI_V<sceNetInetGetPspError>,    "sceNetInetGetPspError",           'i', ""       },
	{0XE247B6D6, &WrapI_IUU<sceNetInetGetpeername>,  "sceNetInetGetpeername",           'i', "ixx"    },
	{0X162E6FD5, &WrapI_IUU<sceNetInetGetsockname>,  "sceNetInetGetsockname",           'i', "ixx"    },
	{0X80A21ABD, &WrapI_I<sceNetInetSocketAbort>,    "sceNetInetSocketAbort",           'i', "i"      },
	{0X39B0C7D3, nullptr,                            "sceNetInetGetUdpcbstat",          '?', ""       },
	{0XB3888AD4, nullptr,                            "sceNetInetGetTcpcbstat",          '?', ""       },
};

const HLEFunction sceNetApctl[] = {
	{0XCFB957C6, &WrapI_I<sceNetApctlConnect>,					"sceNetApctlConnect",              'i', "i"    },
	{0X24FE91A1, &WrapI_V<sceNetApctlDisconnect>,				"sceNetApctlDisconnect",           'i', ""     },
	{0X5DEAC81B, &WrapI_U<sceNetApctlGetState>,					"sceNetApctlGetState",             'i', "x"    },
	{0X8ABADD51, &WrapU_UU<sceNetApctlAddHandler>,				"sceNetApctlAddHandler",           'x', "xx"   },
	{0XE2F91F9B, &WrapI_II<sceNetApctlInit>,					"sceNetApctlInit",                 'i', "ii"   },
	{0X5963991B, &WrapI_U<sceNetApctlDelHandler>,				"sceNetApctlDelHandler",           'i', "x"    },
	{0XB3EDD0EC, &WrapI_V<sceNetApctlTerm>,						"sceNetApctlTerm",                 'i', ""     },
	{0X2BEFDF23, &WrapI_IU<sceNetApctlGetInfo>,					"sceNetApctlGetInfo",              'i', "ix"   },
	{0XA3E77E13, &WrapI_V<sceNetApctlScanSSID2>,				"sceNetApctlScanSSID2",            'i', ""     },
	{0XE9B2E5E6, &WrapI_V<sceNetApctlScanUser>,                 "sceNetApctlScanUser",             'i', ""     },
	{0XF25A5006, &WrapI_UUUU<sceNetApctlGetBSSDescIDList2>,     "sceNetApctlGetBSSDescIDList2",    'i', "xxxx" },
	{0X2935C45B, &WrapI_IIU<sceNetApctlGetBSSDescEntry2>,       "sceNetApctlGetBSSDescEntry2",     'i', "iix"  },
	{0X04776994, &WrapI_IIU<sceNetApctlGetBSSDescEntryUser>,    "sceNetApctlGetBSSDescEntryUser",  'i', "iix"  },
	{0X6BDDCB8C, &WrapI_UU<sceNetApctlGetBSSDescIDListUser>,    "sceNetApctlGetBSSDescIDListUser", 'i', "xx"   },
	{0X7CFAB990, &WrapI_UU<sceNetApctlAddInternalHandler>,      "sceNetApctlAddInternalHandler",   'i', "xx"   },
	{0XE11BAFAB, &WrapI_U<sceNetApctlDelInternalHandler>,       "sceNetApctlDelInternalHandler",   'i', "x"    },
	{0XA7BB73DF, &WrapI_UU<sceNetApctl_A7BB73DF>,               "sceNetApctl_A7BB73DF",            'i', "xx"   },
	{0X6F5D2981, &WrapI_U<sceNetApctl_6F5D2981>,                "sceNetApctl_6F5D2981",            'i', "x"    },
	{0X69745F0A, &WrapI_I<sceNetApctl_lib2_69745F0A>,           "sceNetApctl_lib2_69745F0A",       'i', "i"    },
	{0X4C19731F, &WrapI_IU<sceNetApctl_lib2_4C19731F>,          "sceNetApctl_lib2_4C19731F",       'i', "ix"   },
	{0XB3CF6849, &WrapI_V<sceNetApctlScan>,                     "sceNetApctlScan",                 'i', ""     },
	{0X0C7FFA5C, &WrapI_UU<sceNetApctlGetBSSDescIDList>,        "sceNetApctlGetBSSDescIDList",     'i', "xx"   },
	{0X96BEB231, &WrapI_IIU<sceNetApctlGetBSSDescEntry>,        "sceNetApctlGetBSSDescEntry",      'i', "iix"  },
	{0XC20A144C, &WrapI_IU<sceNetApctl_lib2_C20A144C>,          "sceNetApctl_lib2_C20A144C",       'i', "ix"   },
	// Fake function for PPSSPP's use.
	{0X756E6F10, &WrapV_V<__NetApctlCallbacks>,                 "__NetApctlCallbacks",             'v', ""     },
};

const HLEFunction sceWlanDrv[] = {
	{0XD7763699, &WrapU_V<sceWlanGetSwitchState>,    "sceWlanGetSwitchState",           'x', ""     },
	{0X0C622081, &WrapU_U<sceWlanGetEtherAddr>,      "sceWlanGetEtherAddr",             'x', "x"    },
	{0X93440B11, &WrapU_V<sceWlanDevIsPowerOn>,      "sceWlanDevIsPowerOn",             'x', ""     },
};

// see http://www.kingx.de/forum/showthread.php?tid=35164
const HLEFunction sceNetUpnp[] = {
	{0X27045362, &WrapI_U<sceNetUpnpGetNatInfo>,     "sceNetUpnpGetNatInfo",            'i', "x"    },
	{0X3432B2E5, &WrapI_V<sceNetUpnpStart>,          "sceNetUpnpStart",                 'i', ""     },
	{0X3E32ED9E, &WrapI_V<sceNetUpnpStop>,           "sceNetUpnpStop",                  'i', ""     },
	{0X540491EF, &WrapI_V<sceNetUpnpTerm>,           "sceNetUpnpTerm",                  'i', ""     },
	{0XE24220B5, &WrapI_II<sceNetUpnpInit>,          "sceNetUpnpInit",                  'i', "ii"   },
	{0X8513C6D1, &WrapI_UUU<sceNetUpnp_8513C6D1>,    "sceNetUpnp_8513C6D1",             'i', "xxx"  },
	{0XFDA78483, &WrapI_V<sceNetUpnp_FDA78483>,      "sceNetUpnp_FDA78483",             'i', ""     },
	{0X1038E77A, &WrapI_U<sceNetUpnp_1038E77A>,      "sceNetUpnp_1038E77A",             'i', "x"    },
};

const HLEFunction sceNetIfhandle[] = {
	{0xC80181A2, &WrapI_UU<sceNetGetDropRate>,     "sceNetGetDropRate",                 'i', "pp" },
	{0xFD8585E1, &WrapI_UU<sceNetSetDropRate>,     "sceNetSetDropRate",                 'i', "ii" },
};

void Register_sceNet() {
	RegisterModule("sceNet", ARRAY_SIZE(sceNet), sceNet);
	RegisterModule("sceNetResolver", ARRAY_SIZE(sceNetResolver), sceNetResolver);
	RegisterModule("sceNetInet", ARRAY_SIZE(sceNetInet), sceNetInet);
	RegisterModule("sceNetApctl", ARRAY_SIZE(sceNetApctl), sceNetApctl);
}

// Alias of sceNetApctl, used by SCEJ PSP Browser (UTST-99261)
void Register_sceNetApctl_internal_user() {
	RegisterModule("sceNetApctl_internal_user", ARRAY_SIZE(sceNetApctl), sceNetApctl);
}

void Register_sceWlanDrv() {
	RegisterModule("sceWlanDrv", ARRAY_SIZE(sceWlanDrv), sceWlanDrv);
}

void Register_sceNetUpnp() {
	RegisterModule("sceNetUpnp", ARRAY_SIZE(sceNetUpnp), sceNetUpnp);
}

void Register_sceNetIfhandle() {
	RegisterModule("sceNetIfhandle", ARRAY_SIZE(sceNetIfhandle), sceNetIfhandle);
}
