#include <cstdlib>
#include <soy/init.h>
#include <soy/Timer.h>
#include <soy/Viewport.h>
#include <soy/vec2.h>
#include <soy/util.h>
#include <ode/ode.h>
#include <GL/glut.h>
#include <string>
#include <sstream>
#include <list>
#include <set>
#include <iostream>

#include "Ball.h"
#include "GameMode.h"

const double DT = 1/60.0;

void draw_circle(double radius = 1);
void rot_quat(const dQuaternion q);
void spawn_enemy(vec2 pos = vec2());

SoyInit INIT;
Viewport VIEW(vec2(0,16), vec2(48,36));
vec2 MOUSE;

GameMode* MODE = 0;

void init()
{
	srand(time(NULL));
	
	INIT.set_fullscreen();
	INIT.init();
	SDL_ShowCursor(0);
	VIEW.activate();
}

bool SHOOTING = false;

void events()
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (MODE->events(e)) break;

		if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
			SDL_Quit();
			exit(0);
		}
	}

	int mx, my;
	SDL_GetMouseState(&mx, &my);
	MOUSE = coord_convert(INIT.pixel_view(), VIEW, vec2(mx, my));
}

void reset() {
	delete MODE;
	MODE = new GravityMode;
}

int main()
{
	FrameRateLockTimer timer(DT);
	init();
	reset();
	
	while (true) {
		events();
		MODE->step();

		glClear(GL_COLOR_BUFFER_BIT);
		MODE->draw();
		SDL_GL_SwapBuffers();
		
		timer.lock();
	}
}
