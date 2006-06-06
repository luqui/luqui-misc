#ifndef __TIMER_H__
#define __TIMER_H__

#include <SDL.h>

class Timer
{
public:
	Timer() : prevtime_(SDL_GetTicks()) { }
	
	num get_time_diff() {
		Uint32 curtime = SDL_GetTicks();
		num ret = num(curtime - prevtime_) / 1000;
		prevtime_ = curtime;
		return ret;
	}
private:
	Uint32 prevtime_;
};

#endif
