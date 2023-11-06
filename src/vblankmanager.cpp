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

inline bool __attribute__((always_inline)) _isinf(double val)
{
#ifndef __clang__
	return __builtin_isinf(val);
#else
	return __builtin_isfpclass(val, __FPCLASS_POSINF+_FPCLASS_NEGINF);
#endif
}

inline void cpu_pause(void)
{
#if !defined(__clang__)			
# if defined(__x86_64__) || defined(__i386__)
	__builtin_ia32_pause();
# else
#  if defined(__aarch64__) || defined(__arm__) //GCC doesn't have an intrinsic for aarch64 yield instruction
	asm volatile("yield"); //https://stackoverflow.com/a/70076751
#  elif __has_builtin(__sync_synchronize)
	__sync_synchronize(); //close enough to a pause intrinsic
	__sync_synchronize();
	__sync_synchronize();
#
#else
# if defined(__x86_64__) || defined(__i386__)
	_mm_pause();
# else
#  if defined(__aarch64__) || defined(__arm__)
	asm volatile("yield"); //https://stackoverflow.com/a/70076751
#  elif __has_builtin(__sync_synchronize)
	__sync_synchronize(); //close enough to a pause intrinsic
	__sync_synchronize();
	__sync_synchronize();
#  endif
# endif
#  endif
# endif	
#endif
}

#include <climits>
inline int __attribute__((const, always_inline)) heaviside(const int v)
{
	return 1 ^ ((unsigned int)v >> (sizeof(int) * CHAR_BIT - 1)); //credit: http://www.graphics.stanford.edu/~seander/bithacks.html#CopyIntegerSign
}



// The minimum drawtime to use when we are compositing.
// Getting closer and closer to vblank when compositing means that we can get into
// a feedback loop with our clocks. Pick a sane minimum draw time.
const uint64_t g_uVBlankDrawTimeMinCompositing = 2'400'000;

#define VBLANK_DEBUG

inline int __attribute__((const)) median(const uint16_t l, const uint16_t r) //credit for this function: https://www.geeksforgeeks.org/interquartile-range-iqr/
{

    int n = (int)r - (int)l + 1;

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
    	sum += ( ((uint64_t) a[i]) * 500 ) << 1;
    }
    return sum/(r3 - r1);
}
#undef med

#ifdef __clang__
uint64_t __attribute__((optimize("-fno-unsafe-math-optimizations"), hot )) vblank_next_target( const uint64_t offset)
#else
uint64_t __attribute__((optimize("-fno-unsafe-math-optimizations","-fno-trapping-math", "-fsplit-paths","-fsplit-loops","-fipa-pta","-ftree-partial-pre","-fira-hoist-pressure","-fdevirtualize-speculatively","-fgcse-after-reload","-fgcse-sm","-fgcse-las"), hot )) vblank_next_target( const uint64_t offset )
#endif
{
	const int refresh = g_nNestedRefresh ? g_nNestedRefresh : g_nOutputRefresh;
	const std::lldiv_t div = std::lldiv( 1'000'000'000ll, (long long)refresh);
	const uint64_t nsecInterval = (uint64_t)div.quot;
	
	uint64_t lastVblank = g_lastVblank - offset;
        assert(lastVblank <= std::max( (uint64_t)g_lastVblank,offset));
        
	uint64_t now = get_time_in_nanos();
	uint64_t targetPoint = lastVblank + nsecInterval;
	uint64_t copy_targetPoint = targetPoint;
	if ( (int64_t)targetPoint >= 0 && (int64_t)nsecInterval >= 0 )
	{
		assert( (targetPoint + nsecInterval) >= (uint64_t) abs((int64_t)targetPoint - (int64_t)nsecInterval) );
	}
	while ( targetPoint < now )
	{       
		targetPoint += nsecInterval;
	}
        
        assert(targetPoint <= targetPoint+( ( (long)(targetPoint-copy_targetPoint)*div.rem) / nsecInterval));
	return targetPoint+(uint64_t)(((long)(targetPoint-copy_targetPoint)*div.rem)/nsecInterval);
}


#ifdef __clang__
void __attribute__((optimize("-fno-unsafe-math-optimizations"), hot )) vblankThreadRun( const bool neverBusyWait, const bool alwaysBusyWait, const long double g_nsPerTick_long  )
#else
void __attribute__((optimize("-fno-unsafe-math-optimizations","-fno-trapping-math", "-fsplit-paths","-fsplit-loops","-fipa-pta","-ftree-partial-pre","-fira-hoist-pressure","-fdevirtualize-speculatively","-fgcse-after-reload","-fgcse-sm","-fgcse-las"), hot )) vblankThreadRun( const bool neverBusyWait, const bool alwaysBusyWait, const long double g_nsPerTick_long  )
#endif
{
	pthread_setname_np( pthread_self(), "gamescope-vblk" );

	// Start off our average with our starting draw time.
	uint64_t rollingMaxDrawTime = g_uStartingDrawTime;

	const uint64_t range = g_uVBlankRateOfDecayMax;
	uint8_t sleep_cycle = 0;
	bool slept=false;

	uint32_t skipped_sleep_after_vblank=0;
	
	
	const double g_nsPerTick = (double) g_nsPerTick_long;
	std::cout << "g_nsPerTick: " << g_nsPerTick << "\n";
	
	uint16_t drawtimes[64] = {1};
	uint16_t drawtimes_pending[64];
	std::fill_n(drawtimes, 64, (uint16_t)(((1'000'000'000ul / (g_nNestedRefresh ? g_nNestedRefresh : g_nOutputRefresh)) >> 1)/500 )  );
	int index=0;

	uint64_t centered_mean = 1'000'000'000ul / (g_nNestedRefresh ? g_nNestedRefresh : g_nOutputRefresh);
	uint64_t max_drawtime=2*centered_mean;
	
	
	const uint32_t sleep_weights[2] = {75, 25};
	int64_t vblank_begin=0;
	uint64_t time_start = get_time_in_nanos();
	uint64_t counter = 0;
	uint64_t lastDrawTime = g_uVblankDrawTimeNS;
	uint64_t first_cycle_offset = 0;
	
	while ( true )
	{
		sleep_cycle++;
		if (sleep_cycle < 2)
			vblank_begin=get_time_in_nanos();

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
		const double vblank_adj_factor = 60.0 / ( (double)((std::max(refresh,g_nOutputRefresh))) );
		
		uint64_t drawTime;
		uint64_t offset;
		
		uint64_t second_sleep_adj_wait = 0;
		
		bool bVRR = drm_get_vrr_in_use( &g_DRM );
		if ( !bVRR )
		{
			const uint64_t alpha = g_uVBlankRateOfDecayPercentage;
			
			if (sleep_cycle < 2)
				drawTime = g_uVblankDrawTimeNS;
			
			
			if ( sleep_cycle < 2 && g_bCurrentlyCompositing )
				drawTime = fmax(drawTime, g_uVBlankDrawTimeMinCompositing);
			if (sleep_cycle < 2)
				drawtimes_pending[index] = (uint16_t)( (drawTime >> 1)/500 );
			
			
			if (sleep_cycle > 1)
			{	
				rollingMaxDrawTime = ( ( alpha * rollingMaxDrawTime ) + ( range - alpha ) * drawTime ) / (range);
				g_uRollingMaxDrawTime.store(rollingMaxDrawTime, std::memory_order_relaxed);
			}
			else
			{
				double delta_check = pow(fmax((double)( fabs((int64_t)lastDrawTime - (int64_t)drawTime)), 1.0 )/100000.0, 2);
				double delta = fmax( delta_check * (double)(heaviside( (int64_t)nsecInterval/1000000 - ((int) round(2.0*delta_check)))) , 1);
				//						^ branchless way of checking if value delta_check is so large that it'll mess up
				//						  the rollingMaxDrawTime calculations
				double ratio = ((double)drawTime) / ( fmax( ((double) heaviside( (int64_t) nsecInterval - (int64_t)lastDrawTime)) * ( (double) lastDrawTime), drawTime ) );
				rollingMaxDrawTime = 
				  fmin(
				   ( ( alpha * rollingMaxDrawTime ) + ( range - alpha ) * drawTime ) / (range)
				   , (uint64_t)(llroundl( (double)centered_mean 
				      * ratio /( delta)			     
		                                        )
		                               )
		                          );
		        	std::cout << "delta= " << delta << "\n";
				std::cout << "rollingMaxDrawTime after using fmin: " << rollingMaxDrawTime << "\n";
			}
			rollingMaxDrawTime = std::clamp(centered_mean/4, rollingMaxDrawTime, nsecInterval+nsecInterval/10);
			std::cout << "rollingMaxDrawTime after using std::clamp: " << rollingMaxDrawTime << "\n";
			
			offset = rollingMaxDrawTime + redZone;
			if (sleep_cycle > 1)
			{
				offset = std::clamp(std::min(nsecInterval, centered_mean)-nsecInterval/25, offset, nsecInterval+nsecInterval/20);
				if (offset > first_cycle_offset)
				{
					second_sleep_adj_wait = (offset - first_cycle_offset) * sleep_weights[0] / 100;
				}
			}
			else
			{
				offset = std::clamp(std::min(nsecInterval, centered_mean)-nsecInterval/5, offset , nsecInterval+nsecInterval/5);
				first_cycle_offset=offset;
			}	
				
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
					  	((uint64_t)(std::max(  (uint16_t)((max_drawtime>>1)/500), *std::max_element(std::begin(drawtimes), std::end(drawtimes)))))
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

#define HMMM(expr) __builtin_expect_with_probability(expr, 1, .15) //hmmm has slightly higher probability than meh
#define MEH(expr) __builtin_expect_with_probability(expr, 1, .02)
		if ( !neverBusyWait && ( alwaysBusyWait || sleep_cycle > 1 ) 
		&& offset*sleep_weights[sleep_cycle-1] / (100ll) < 1'000'000ll)
		{
			
			int64_t diff;
			double res;
			double check_this_first = 0.0;
			long double check_this = 0.0L;
			
			uint64_t prev = readCycleCount();
			
			double compared_to = (double) ( second_sleep_adj_wait + offset*sleep_weights[sleep_cycle-1] / (100ll) );
			
			do
			{
				res = DBL_MAX;
				
				cpu_pause();
				
				diff = (int64_t)readCycleCount() - (int64_t)prev;
				if ( diff < 0)
				{
					std::cout << "oh noes\n";
					continue; // in case tsc counter resets or something
				}
				
				check_this_first = (double)diff * g_nsPerTick;
				if ( HMMM(_isinf(check_this_first)) )
				{
					check_this = (long double)diff * g_nsPerTick_long;
					if ( MEH(std::fpclassify(check_this) == FP_INFINITE) ) //meh and hmmm: compiler hints that this branch is unlikely to occur
					{						       //     hopefully might reduce fruitless speculative execution
						break;
					}
					res = ( ( std::fpclassify(check_this) == FP_NORMAL && check_this <= DBL_MAX) ? check_this :  DBL_MAX);
				}
				res = check_this_first;
			}
			while ( res < compared_to );

			slept=false;
			targetPoint = vblank_next_target( offset );
		}
		else
		{
			slept=true;
			
			
			targetPoint = vblank_next_target( second_sleep_adj_wait + offset*sleep_weights[sleep_cycle-1] / (100ll) );
			
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
			std::cout << "vblank cycle time: " << ( (long double)(get_time_in_nanos()-vblank_begin) )/1'000'000.0L << "ms\n";
			counter++;
		}
		vblank_begin=0;
		
		uint64_t this_time=(get_time_in_nanos() - time_start)/1'000'000'000ul;
		if ( this_time > 5)
		{
			std::cout << counter << " vblanks sent in " << this_time << " seconds\n";
			time_start=get_time_in_nanos();
		}
		
		
		const uint64_t adjusted_extra_sleep = (uint64_t)llroundl(1'000'000.0*std::sqrt(vblank_adj_factor));
		// Get on the other side of it now
		if ( !alwaysBusyWait && (neverBusyWait || !slept || skipped_sleep_after_vblank >= 3)  )
		{
			skipped_sleep_after_vblank=0;
			sleep_for_nanos( offset + second_sleep_adj_wait + adjusted_extra_sleep );
		}
		else
		{
			
			int64_t diff;
			double res;
			double check_this_first = 0.0;
			long double check_this = 0.0L;
			
			uint64_t prev = readCycleCount();
			
			double compared_to = (double) ( offset + second_sleep_adj_wait + adjusted_extra_sleep + first_cycle_offset * sleep_weights[1] / (sleep_weights[0]) );
			do
			{
				res = DBL_MAX;
				
				cpu_pause();
				
				diff = (int64_t)readCycleCount() - (int64_t)prev;
				if (diff < 0)
				{
					std::cout << "oh noes\n";
					continue; // in case tsc counter resets or something
				}
				
				check_this_first = (double)diff * g_nsPerTick;
				if ( HMMM(_isinf(check_this_first)) )
				{
					check_this = (long double)diff * g_nsPerTick_long;
					if ( MEH(std::fpclassify(check_this) == FP_INFINITE) ) //meh and hmmm: compiler hints that this branch is unlikely to occur
					{						       //     hopefully might reduce fruitless speculative execution
						break;
					}
					res = ( ( std::fpclassify(check_this) == FP_NORMAL && check_this <= DBL_MAX) ? check_this :  DBL_MAX);
				}
				res = check_this_first;
				
			}
			while (res <  compared_to);		
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

int vblank_init( const bool never_busy_wait, const bool always_busy_wait )
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
	const long double g_nsPerTick_long = getNsPerTick();
	
	#define NEVER_BUSY_WAIT true,false,CANT_USE_CPU_TIMER
	#define BALANCED_BUSY_WAIT false,false
	#define ALWAYS_BUSY_WAIT false,true
	
	if ( never_busy_wait || g_nsPerTick_long == CANT_USE_CPU_TIMER) {
		std::thread vblankThread( vblankThreadRun, NEVER_BUSY_WAIT );
		vblankThread.detach();
	}
	else if (always_busy_wait) {
		std::thread vblankThread( vblankThreadRun, ALWAYS_BUSY_WAIT, g_nsPerTick_long );
		vblankThread.detach();
	}
	else {
		std::thread vblankThread( vblankThreadRun, BALANCED_BUSY_WAIT, g_nsPerTick_long );
		vblankThread.detach();
	}
	
	return g_vblankPipe[ 0 ];
}

void vblank_mark_possible_vblank( uint64_t nanos )
{
	g_lastVblank = nanos;
}
