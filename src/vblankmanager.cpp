// Try to figure out when vblank is and notify steamcompmgr to render some time before it

#include <cstdint>
#include <mutex>
#include <thread>
#include <future>
#include <vector>
#include <chrono>
#include <atomic>
#include <condition_variable>
#include <algorithm>
#include <cstdlib>
#include <cfloat>
#include <cmath>

#include <assert.h>
#include <fcntl.h>
#include <unistd.h>

#include "gpuvis_trace_utils.h"

#include "vblankmanager.hpp"
#include "steamcompmgr.hpp"
#include "wlserver.hpp"
#include "main.hpp"
#include "drm.hpp"
#include <iostream>

#if HAVE_OPENVR
#include "vr_session.hpp"
#endif


#include "nominalFrequency.cc"

static int g_vblankPipe[2];

std::atomic<uint64_t> g_lastVblank;

// 3ms by default -- a good starting value.
const uint64_t g_uStartingDrawTime = 3'000'000;

// This is the last time a draw took.
std::atomic<uint64_t> g_uVblankDrawTimeNS = { g_uStartingDrawTime };

// 1.3ms by default. (g_uDefaultMinVBlankTime)
// This accounts for some time we cannot account for (which (I think) is the drm_commit -> triggering the pageflip)
// It would be nice to make this lower if we can find a way to track that effectively
// Perhaps the missing time is spent elsewhere, but given we track from the pipe write
// to after the return from `drm_commit` -- I am very doubtful.
uint64_t g_uMinVblankTime = g_uDefaultMinVBlankTime;

// Tuneable
// 0.3ms by default. (g_uDefaultVBlankRedZone)
// This is the leeway we always apply to our buffer.
uint64_t g_uVblankDrawBufferRedZoneNS = g_uDefaultVBlankRedZone;

// Tuneable
// 93% by default. (g_uVBlankRateOfDecayPercentage)
// The rate of decay (as a percentage) of the rolling average -> current draw time
uint64_t g_uVBlankRateOfDecayPercentage = g_uDefaultVBlankRateOfDecayPercentage;

const uint64_t g_uVBlankRateOfDecayMax = 1000;

static std::atomic<uint64_t> g_uRollingMaxDrawTime = { g_uStartingDrawTime };

std::atomic<bool> g_bCurrentlyCompositing = { false };

// The minimum drawtime to use when we are compositing.
// Getting closer and closer to vblank when compositing means that we can get into
// a feedback loop with our clocks. Pick a sane minimum draw time.
const uint64_t g_uVBlankDrawTimeMinCompositing = 2'400'000;

//#define VBLANK_DEBUG

uint64_t __attribute__((optimize("-fno-unsafe-math-optimizations") )) vblank_next_target( uint64_t offset )
{
	
	const int refresh = g_nNestedRefresh ? g_nNestedRefresh : g_nOutputRefresh;
	std::lldiv_t div = std::lldiv( 1'000'000'000ll, static_cast<long long>(refresh));
	const uint64_t nsecInterval = static_cast<uint64_t>(div.quot);
	
	uint64_t lastVblank = g_lastVblank - offset;
        assert(lastVblank <= std::max( static_cast<uint64_t>(g_lastVblank),offset));
        
	uint64_t now = get_time_in_nanos();
	uint64_t targetPoint = lastVblank + nsecInterval;
	uint64_t copy_targetPoint = targetPoint;
	if ( static_cast <int64_t>(targetPoint) >= 0 && static_cast<int64_t>(nsecInterval) >= 0 )
	{
		assert( (targetPoint + nsecInterval) >= static_cast<uint64_t>(abs(static_cast <int64_t>(targetPoint) - static_cast<int64_t>(nsecInterval))) );
	}
	while ( targetPoint < now )
	{
		/*if ( static_cast <int64_t>(targetPoint) >= 0 && static_cast<int64_t>(nsecInterval) >= 0 )
		{
			assert( (targetPoint + nsecInterval) >= static_cast<uint64_t>(abs(static_cast <int64_t>(targetPoint) - static_cast<int64_t>(nsecInterval))) );
		}*/
	        
		targetPoint += nsecInterval;
	}
        
        assert(targetPoint <= targetPoint+(std::ldiv_t( static_cast<long>(targetPoint-copy_targetPoint)*div.rem, nsecInterval).quot));
	return targetPoint+static_cast<uint64_t>((std::lldiv( static_cast<long>(targetPoint-copy_targetPoint)*div.rem, nsecInterval).quot));
}

#include <sys/prctl.h>
#include <linux/capability.h>
long double __attribute__((optimize("-fno-unsafe-math-optimizations") )) getFactor(void)
{
	if ( prctl(PR_CAPBSET_READ, CAP_SYS_NICE, NULL, NULL, NULL) == 1)
		prctl(PR_CAPBSET_DROP, CAP_SYS_NICE, NULL, NULL, NULL);
	return static_cast<long double>(getNsPerTick());
}

void __attribute__((optimize("-fno-unsafe-math-optimizations") )) vblankThreadRun( void )
{
	pthread_setname_np( pthread_self(), "gamescope-vblk" );

	// Start off our average with our starting draw time.
	uint64_t rollingMaxDrawTime = g_uStartingDrawTime;

	const uint64_t range = g_uVBlankRateOfDecayMax;
	uint8_t sleep_cycle = 0;
	bool slept=false;
	uint64_t prev_evaluation = INT_MAX;
	uint32_t skipped_sleep_after_vblank=0;
	
	auto handle = std::async(std::launch::async, getFactor);
	const long double g_nsPerTick = handle.get();
	
	while ( true )
	{
		sleep_cycle++;
		const int refresh = g_nNestedRefresh ? g_nNestedRefresh : g_nOutputRefresh;
		const uint64_t nsecInterval = 1'000'000'000ul / refresh;
		// The redzone is relative to 60Hz, scale it by our
		// target refresh so we don't miss submitting for vblank in DRM.
		// (This fixes 4K@30Hz screens)
		const uint64_t nsecToSec = 1'000'000'000ul;
		const drm_screen_type screen_type = drm_get_screen_type( &g_DRM );
		const uint64_t redZone = screen_type == DRM_SCREEN_TYPE_INTERNAL
			? g_uVblankDrawBufferRedZoneNS
			: ( g_uVblankDrawBufferRedZoneNS * 60 * nsecToSec ) / ( refresh * nsecToSec );

		uint64_t offset;
		bool bVRR = drm_get_vrr_in_use( &g_DRM );
		uint64_t drawslice=0;
		if ( !bVRR )
		{
			const uint64_t alpha = g_uVBlankRateOfDecayPercentage;
			
			uint64_t drawTime = g_uVblankDrawTimeNS.load(std::memory_order_acquire);
			
			
			if ( g_bCurrentlyCompositing )
				drawTime = std::max(drawTime, g_uVBlankDrawTimeMinCompositing);
			
			
			// This is a rolling average when drawTime < rollingMaxDrawTime,
			// and a a max when drawTime > rollingMaxDrawTime.
			// This allows us to deal with spikes in the draw buffer time very easily.
			// eg. if we suddenly spike up (eg. because of test commits taking a stupid long time),
			// we will then be able to deal with spikes in the long term, even if several commits after
			// we get back into a good state and then regress again.

			// If we go over half of our deadzone, be more defensive about things.
			assert( int64_t(drawTime) >= 0);
			if ( int64_t(drawTime) - int64_t(redZone / 2) > int64_t(rollingMaxDrawTime) )
				rollingMaxDrawTime = drawTime;
			else
			{
				drawslice= ( range - alpha ) * drawTime;
				assert( (alpha <= alpha * rollingMaxDrawTime) || (rollingMaxDrawTime==0) );
				assert( drawTime <= ( range - alpha ) * drawTime || (drawTime == 0) );
				
				assert( ( alpha * rollingMaxDrawTime )/range <= ( ( alpha * rollingMaxDrawTime ) + ( range - alpha ) * drawTime ) / range
				      &&( alpha * rollingMaxDrawTime ) <= ( ( alpha * rollingMaxDrawTime ) + ( range - alpha ) * drawTime ) 
				      ); 
				rollingMaxDrawTime = ( ( alpha * rollingMaxDrawTime ) + ( range - alpha ) * drawTime ) / range;
			}

			// If we need to offset for our draw more than half of our vblank, something is very wrong.
			// Clamp our max time to half of the vblank if we can.
			rollingMaxDrawTime = std::min( rollingMaxDrawTime, nsecInterval - redZone );

			g_uRollingMaxDrawTime = rollingMaxDrawTime;

			offset = rollingMaxDrawTime + redZone;
			assert(offset > rollingMaxDrawTime);
			assert(offset > redZone);
		}
		else
		{
			// VRR:
			// Just ensure that if we missed a frame due to already
			// having a page flip in-flight, that we flush it out with this.
			// Nothing fancy needed, just need to get on the other side of the page flip.
			//
			// We don't use any of the rolling times due to them varying given our
			// 'vblank' time is varying.
			g_uRollingMaxDrawTime = g_uStartingDrawTime;

			offset = 1'000'000 + redZone;
		}

#ifdef VBLANK_DEBUG
		// Debug stuff for logging missed vblanks
		static uint64_t vblankIdx = 0;
		static uint64_t lastDrawTime = g_uVblankDrawTimeNS;
		static uint64_t lastOffset = g_uVblankDrawTimeNS + redZone;

		if ( vblankIdx++ % 300 == 0 || drawTime > lastOffset )
		{
			if ( drawTime > lastOffset )
				fprintf( stderr, " !! missed vblank " );

			fprintf( stderr, "redZone: %.2fms decayRate: %lu%% - rollingMaxDrawTime: %.2fms lastDrawTime: %.2fms lastOffset: %.2fms - drawTime: %.2fms offset: %.2fms\n",
				redZone / 1'000'000.0,
				g_uVBlankRateOfDecayPercentage,
				rollingMaxDrawTime / 1'000'000.0,
				lastDrawTime / 1'000'000.0,
				lastOffset / 1'000'000.0,
				drawTime / 1'000'000.0,
				offset / 1'000'000.0 );
		}

		lastDrawTime = drawTime;
		lastOffset = offset;
#endif
		uint64_t targetPoint;
		if ( ((offset*( (refresh/g_nOutputRefresh) ))/(2*sleep_cycle)) < 1'000'000l + drawslice * drawslice)
		{
			std::cout << "sleep_cycle=" << sleep_cycle << "\n"
			<< "\n"
			<< "(offset/(sleep_cycle)) = " << (offset/(sleep_cycle)) << "\n";
		}
		
		if (  ((offset*( (refresh/g_nOutputRefresh) ))/(2*sleep_cycle)) < 1'000'000l + drawslice && prev_evaluation > ((offset*( (refresh)/g_nOutputRefresh))/(2*sleep_cycle)))
		{
			std::cout << "sleep_cycle=" << sleep_cycle << "\n"
			<< "\n"
			<< "busy waiting :DDD -- (offset/(sleep_cycle)) = " << (offset/(sleep_cycle)) << "\n";
			int64_t diff;
			long long res;
			long double check_this = 0;
			uint64_t prev = readCycleCount();
			do
			{
				res = INT_MAX;
#ifdef __GNUC__			
				__builtin_ia32_pause();
#else
				_mm_pause();
#endif
				diff = static_cast<int64_t>(readCycleCount()) - static_cast<int64_t>(prev);
				if ( diff < 0)
				{
					std::cout << "oh noes\n";
					continue; // in case tsc counter resets or something
				}
				
				check_this = static_cast<long double>(diff) * g_nsPerTick;
				
				res = (std::fpclassify(check_this) == FP_NORMAL) ? llroundl(check_this) : INT_MAX;
				std::cout << "std::fpclassify(check_this): " << std::fpclassify(check_this) << "\n";
			}
			while ( static_cast<uint64_t> (res) < ((offset*( refresh/g_nOutputRefresh))/(2*sleep_cycle)));
			slept=false;
			targetPoint = vblank_next_target( offset );
			prev_evaluation=((offset*( refresh/g_nOutputRefresh))/(2*sleep_cycle));
			std::cout << "exited busy wait loop\n";
		}
		else
		{
			slept=true;
			
			targetPoint = vblank_next_target( ((offset*( refresh/g_nOutputRefresh))/(2*sleep_cycle)) );

			sleep_until_nanos( targetPoint );
			targetPoint = vblank_next_target(offset);
		}
		
		if (sleep_cycle < 2)
		{
			continue;
		}
		VBlankTimeInfo_t time_info =
		{
//			.target_vblank_time = targetPoint + offset/(2*sleep_cycle),
			.target_vblank_time = targetPoint + offset,
			.pipe_write_time    = get_time_in_nanos(),
		};

		ssize_t ret = write( g_vblankPipe[ 1 ], &time_info, sizeof( time_info ) );
		if ( ret <= 0 )
		{
			perror( "vblankmanager: write failed" );
		}
		else
		{
			gpuvis_trace_printf( "sent vblank" );
		}
		
		// Get on the other side of it now
		if (!slept)
		{
			skipped_sleep_after_vblank=0;
			sleep_for_nanos( (offset + 1'000'000) );
		}
		else if (skipped_sleep_after_vblank < 3)
		{
#ifdef __GNUC__			
			__builtin_ia32_pause();
			__builtin_ia32_pause();
#else
			_mm_pause();
			_mm_pause();
#endif		
			skipped_sleep_after_vblank++;
		}
		else if (slept)
		{
			prev_evaluation=INT_MAX;
		}
		sleep_cycle=0;
		slept=false;
	}
}

#if HAVE_OPENVR
void vblankThreadVR()
{
	pthread_setname_np( pthread_self(), "gamescope-vblkvr" );

	while ( true )
	{
		vrsession_wait_until_visible();

		// Includes redzone.
		vrsession_framesync( ~0u );

		uint64_t now = get_time_in_nanos();

		VBlankTimeInfo_t time_info =
		{
			.target_vblank_time = now + 3'000'000, // not right. just a stop-gap for now.
			.pipe_write_time    = now,
		};

		ssize_t ret = write( g_vblankPipe[ 1 ], &time_info, sizeof( time_info ) );
		if ( ret <= 0 )
		{
			perror( "vblankmanager: write failed" );
		}
		else
		{
			gpuvis_trace_printf( "sent vblank" );
		}
	}
}
#endif

int vblank_init( void )
{
	if ( pipe2( g_vblankPipe, O_CLOEXEC | O_NONBLOCK ) != 0 )
	{
		perror( "vblankmanager: pipe failed" );
		return -1;
	}
	
	g_lastVblank = get_time_in_nanos();

#if HAVE_OPENVR
	if ( BIsVRSession() )
	{
		std::thread vblankThread( vblankThreadVR );
		vblankThread.detach();
		return g_vblankPipe[ 0 ];
	}
#endif

	std::thread vblankThread( vblankThreadRun );
	vblankThread.detach();
	return g_vblankPipe[ 0 ];
}

void vblank_mark_possible_vblank( uint64_t nanos )
{
	g_lastVblank = nanos;
}
