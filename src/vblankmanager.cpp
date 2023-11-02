// Try to figure out when vblank is and notify steamcompmgr to render some time before it

#include <cstdint>
#include <mutex>
#include <thread>
#include <vector>
#include <chrono>
#include <atomic>
#include <condition_variable>
#include <algorithm>
#include <cstdlib>
#include <cfloat>
#include <cmath>
#include <numeric>

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

#define VBLANK_DEBUG

inline int __attribute__((const)) median(const uint16_t l, const uint16_t r) //credit for this function: https://www.geeksforgeeks.org/interquartile-range-iqr/
{

    int n = static_cast<int>(r) - static_cast<int>(l) + 1;

    n = (n + 1) / 2 - 1;

    return n + l;

}

#define med(a,l,r) median(l,r)

inline uint64_t __attribute__((nonnull(1))) IQM(uint16_t* a, const int n) //credit for this function: https://www.geeksforgeeks.org/interquartile-range-iqr/

{

    std::sort(a, a + n);

    int mid_index = med(a, 0, n);

    int r1 = med(a, 0, mid_index);

    int r3 = std::min(med(a, mid_index + 1, n), n);
    
    uint64_t sum=0;
    for (int i = r1; i < r3; i++)
    {
    	sum += ((static_cast<uint64_t> (a[i])) * 500) << 1;
    }
    return sum/(r3 - r1);

}

#ifdef __GNUC__
uint64_t __attribute__((optimize("-fno-unsafe-math-optimizations", "-fsplit-paths","-fsplit-loops","-fipa-pta","-ftree-partial-pre","-fira-hoist-pressure","-fdevirtualize-speculatively","-fgcse-after-reload","-fgcse-sm","-fgcse-las"), hot )) vblank_next_target( const uint64_t offset )
#else
uint64_t __attribute__((optimize("-fno-unsafe-math-optimizations"), hot )) vblank_next_target( const uint64_t offset )
#endif
{
	
	const int refresh = g_nNestedRefresh ? g_nNestedRefresh : g_nOutputRefresh;
	const std::lldiv_t div = std::lldiv( 1'000'000'000ll, static_cast<long long>(refresh));
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
		targetPoint += nsecInterval;
	}
        
        assert(targetPoint <= targetPoint+(std::ldiv_t( static_cast<long>(targetPoint-copy_targetPoint)*div.rem, nsecInterval).quot));
	return targetPoint+static_cast<uint64_t>((std::lldiv( static_cast<long>(targetPoint-copy_targetPoint)*div.rem, nsecInterval).quot));
}

#include <sys/prctl.h>
#include <linux/capability.h>

#ifdef __GNUC__
void __attribute__((optimize("-fno-unsafe-math-optimizations", "-fsplit-paths","-fsplit-loops","-fipa-pta","-ftree-partial-pre","-fira-hoist-pressure","-fdevirtualize-speculatively","-fgcse-after-reload","-fgcse-sm","-fgcse-las"), hot )) vblankThreadRun( void )
#else
void __attribute__((optimize("-fno-unsafe-math-optimizations"), hot )) vblankThreadRun( void )
#endif
{
	pthread_setname_np( pthread_self(), "gamescope-vblk" );

	// Start off our average with our starting draw time.
	uint64_t rollingMaxDrawTime = g_uStartingDrawTime;

	const uint64_t range = g_uVBlankRateOfDecayMax;
	uint8_t sleep_cycle = 0;
	bool slept=false;

	uint32_t skipped_sleep_after_vblank=0;
	
	//if ( prctl(PR_CAPBSET_READ, CAP_SYS_NICE, NULL, NULL, NULL) == 1)
	//	prctl(PR_CAPBSET_DROP, CAP_SYS_NICE, NULL, NULL, NULL);

	long double g_nsPerTick = getNsPerTick();
	std::cout << "g_nsPerTick: " << g_nsPerTick << "\n";
	
	uint16_t drawtimes[64] = {1};
	uint16_t drawtimes_pending[64];
	std::fill_n(drawtimes, 64, static_cast<uint16_t>(((1'000'000'000ul / (g_nNestedRefresh ? g_nNestedRefresh : g_nOutputRefresh)) >> 1)/500 )  );
	int index=0;

	uint64_t centered_mean = 1'000'000'000ul / (g_nNestedRefresh ? g_nNestedRefresh : g_nOutputRefresh);
	uint64_t max_drawtime=2*centered_mean;
	
	
	const uint32_t sleep_weights[2] = {75, 25};
	int64_t vblank_begin=0;
	uint64_t time_start = get_time_in_nanos();
	uint64_t counter = 0;
	while ( true )
	{
		sleep_cycle++;
		if (sleep_cycle < 2)
			vblank_begin=get_time_in_nanos();
		
		long long time_discount = 0;
		
		if (sleep_cycle > 1)
			time_discount=readCycleCount();

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
		const double vblank_adj_factor = 60.0 / static_cast<double>((std::max(refresh,g_nOutputRefresh)));
		
		uint64_t drawTime;
		uint64_t offset;
		
		static uint64_t lastDrawTime = g_uVblankDrawTimeNS;
		
		bool bVRR = drm_get_vrr_in_use( &g_DRM );
		if ( !bVRR )
		{
			
			const uint64_t alpha = g_uVBlankRateOfDecayPercentage;
			
			if (sleep_cycle > 1)
				drawTime = g_uVblankDrawTimeNS.load(std::memory_order_acquire);
			else
				drawTime = g_uVblankDrawTimeNS;
			
			
			if ( g_bCurrentlyCompositing )
				drawTime = std::max(drawTime, g_uVBlankDrawTimeMinCompositing);
			if (sleep_cycle < 2)
				drawtimes_pending[index] = static_cast<uint16_t>( (drawTime >> 1)/500 );
			

			// If we go over half of our deadzone, be more defensive about things.
			//assert( int64_t(drawTime) >= 0);
			//if ( int64_t(drawTime) - int64_t(redZone / 2) > int64_t(rollingMaxDrawTime) )
			//	rollingMaxDrawTime = drawTime;
				
			if (sleep_cycle > 1)
			{	
				//long double roll = 1.1*std::sqrt(vblank_adj_factor)*std::exp(-((.2*std::pow(static_cast<long double>(rollingMaxDrawTime),.666666666666666666)*std::sqrt(vblank_adj_factor)+5*static_cast<long double>(redZone))/10000000.0));
				//std::cout << "std::exp(-(static_cast<long double>(rollingMaxDrawTime)/10000000.0)) = " << roll << "\n";
				//roll =  static_cast<long double>(centered_mean ? (centered_mean) : 3*nsecInterval/2)/(1.0+roll);
				//std::cout << "static_cast<long double>(centered_mean)/(1.0+roll) = " << roll << "\n";
				rollingMaxDrawTime = ( ( alpha * rollingMaxDrawTime ) + ( range - alpha ) * drawTime ) / (range);
				g_uRollingMaxDrawTime.store(rollingMaxDrawTime, std::memory_order_relaxed);
			}
			else
			{
				rollingMaxDrawTime = std::min(( ( alpha * rollingMaxDrawTime ) + ( range - alpha ) * drawTime ) / (range), static_cast<uint64_t>(llroundl( static_cast<double>((centered_mean/2)) * std::pow(static_cast<double>(drawTime)/(std::max(static_cast<double>( std::abs(static_cast<int64_t>(lastDrawTime) - static_cast<int64_t>(drawTime))), 1.0 )), 2))));
			}
			
			offset = rollingMaxDrawTime + redZone;
				
				
			fprintf( stdout, "sleep_cycle=%i offset clamping: ", sleep_cycle );

			fprintf( stdout, "redZone: %.2fms decayRate: %lu%% - rollingMaxDrawTime: %.2fms - drawTime: %.2fms offset: %.2fms\n",
			  redZone / 1'000'000.0,
			  g_uVBlankRateOfDecayPercentage,
			  rollingMaxDrawTime / 1'000'000.0,
			  drawTime / 1'000'000.0,
			  offset / 1'000'000.0 );

			if (sleep_cycle < 2)
				index++;
			
			if ( sleep_cycle < 2 && index >= 64 )
			{
				
				memcpy(drawtimes, drawtimes_pending, 64 * sizeof(drawtimes_pending[0]));
				index=0;
				const uint16_t n = 64; 
				centered_mean = (centered_mean + clamp(2*nsecInterval/3, IQM(drawtimes, n), 5*nsecInterval/3))/2;
				
				max_drawtime = std::min( 
					      (	
					  	(static_cast<uint64_t>(std::max(  static_cast<uint16_t>((max_drawtime>>1)/500), *std::max_element(std::begin(drawtimes), std::end(drawtimes)))))
					      * 500)
					      <<1
					, 8*nsecInterval/3);
			}
			
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
		
		static uint64_t lastOffset = g_uVblankDrawTimeNS + redZone;

		if ( sleep_cycle > 1 && (vblankIdx++ % 300 == 0 || drawTime > lastOffset) )
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


#endif
		uint64_t targetPoint;
		
		if ( static_cast<uint64_t>( llroundl( static_cast<long double>(offset*refresh*sleep_weights[sleep_cycle-1]) / static_cast<long double>(100*g_nOutputRefresh))) < 1'000'000l)
		{
			
			int64_t diff;
			long long res;
			long double check_this = 0;
			uint64_t prev = readCycleCount();
			time_discount = static_cast<int64_t>(prev)-time_discount;
			do
			{
				res = INT_MAX;
#ifdef __GNUC__			
# if !(LOMP_TARGET_ARCH_X86_64)
				__sync_synchronize(); //close enough to a pause intrinsic
				__sync_synchronize();
				__sync_synchronize();
# else	
				__builtin_ia32_pause();
# endif
#else
# if !(LOMP_TARGET_ARCH_X86_64)
#  if __has_builtin(__sync_synchronize)
				__sync_synchronize(); //close enough to a pause intrinsic
				__sync_synchronize();
				__sync_synchronize();
#  endif
# else
				_mm_pause();
# endif	
#endif
				diff = static_cast<int64_t>(readCycleCount()) - static_cast<int64_t>(prev)-time_discount;
				if ( diff < 0)
				{
					std::cout << "oh noes\n";
					continue; // in case tsc counter resets or something
				}
				
				check_this = static_cast<long double>(diff) * g_nsPerTick;
				
				res = (std::fpclassify(check_this) == FP_NORMAL) ? llroundl(check_this) : INT_MAX;
				if (std::fpclassify(check_this) == FP_INFINITE)
				{
					break;
				}
			}
			while ( static_cast<uint64_t> (res) 
			       <  static_cast<uint64_t>( llroundl( 
			      		static_cast<long double>(offset*refresh*sleep_weights[sleep_cycle-1]) 
			      		/ static_cast<long double>(100*g_nOutputRefresh)
			      					 ))
			      );
			time_discount=0;
			slept=false;
			targetPoint = vblank_next_target( static_cast<uint64_t>(llroundl(offset)) );
		}
		else
		{
			slept=true;
			
			targetPoint = vblank_next_target(  static_cast<uint64_t>( llroundl( static_cast<long double>((offset*refresh * sleep_weights[sleep_cycle-1] ) / static_cast<long double>(100*g_nOutputRefresh)) )));
			
			sleep_until_nanos( targetPoint );
			targetPoint = vblank_next_target(offset);
		}
		
		if (sleep_cycle < 2)
		{
			continue;
		}
		
		VBlankTimeInfo_t time_info =
		{
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
			std::cout << "vblank cycle time: " << static_cast<long double>(get_time_in_nanos()-vblank_begin)/1'000'000.0 << "ms\n";
			counter++;
		}
		vblank_begin=0;
		
		uint64_t this_time=(get_time_in_nanos() - time_start)/1'000'000'000ul;
		if ( this_time > 5)
		{
			std::cout << counter++ " vblanks sent in " << this_time << " seconds\n";
			time_start=get_time_in_nanos();
		}
		
		// Get on the other side of it now
		if (!slept)
		{
			skipped_sleep_after_vblank=0;
			sleep_for_nanos( (centered_mean + offset)/2 + 1'000'000ul );
		}
		else if (skipped_sleep_after_vblank < 3)
		{
			int64_t diff;
			long long res;
			long double check_this = 0;
			uint64_t prev = readCycleCount();
			do
			{
				res = INT_MAX;
#ifdef __GNUC__			
# if !(LOMP_TARGET_ARCH_X86_64)
				__sync_synchronize(); //close enough to a pause intrinsic
				__sync_synchronize();
				__sync_synchronize();
# else	
				__builtin_ia32_pause();
# endif
#else
# if !(LOMP_TARGET_ARCH_X86_64)
#  if __has_builtin(__sync_synchronize)
				__sync_synchronize(); //close enough to a pause intrinsic
				__sync_synchronize();
				__sync_synchronize();
#  endif
# else
				_mm_pause();
# endif	
#endif
				diff = static_cast<int64_t>(readCycleCount()) - static_cast<int64_t>(prev);
				if ( diff < 0)
				{
					std::cout << "oh noes\n";
					continue; // in case tsc counter resets or something
				}
				
				check_this = static_cast<long double>(diff) * g_nsPerTick;
				
				res = (std::fpclassify(check_this) == FP_NORMAL) ? llroundl(check_this) : INT_MAX;
				if (std::fpclassify(check_this) == FP_INFINITE)
				{
					break;
				}
			}
			while ( static_cast<uint64_t> (res) < (centered_mean + offset)/2 + 1'000'000ul);		
			skipped_sleep_after_vblank++;
		}
		sleep_cycle=0;
		slept=false;
		lastDrawTime = drawTime;
		lastOffset = offset;
		
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
