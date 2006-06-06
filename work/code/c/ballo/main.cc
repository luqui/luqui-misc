#include "config.h"
#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <cstdlib>
#include <cmath>
#include <ode/ode.h>
#include "vec.h"
#include "physics.h"
#include "Timer.h"

void draw_circle()
{
	glBegin(GL_TRIANGLE_FAN);
	glVertex2d(0,0);
	for (int i = 0; i <= 24; i++) {
		num theta = 2*M_PI*i/24;
		glVertex2d(cos(theta), sin(theta));
	}
	glEnd();
}

class Ballo : public Body
{
public:
	void draw() const {
		glPushMatrix();
		vec mypos = drawing_pos();
		glTranslated(mypos.x, mypos.y, 0);
		draw_circle();
		glPopMatrix();
	}
};

void init_sdl()
{
	SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER);
	SDL_SetVideoMode(800, 600, 0, SDL_OPENGL);

	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	gluOrtho2D(0, 16, 0, 12);
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
}

void draw()
{
}

void step()
{
	dWorldQuickStep(WORLD, 0.01);
}

void events()
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		switch (e.type) {
			case SDL_KEYDOWN:
				if (e.key.keysym.sym == SDLK_ESCAPE) {
					SDL_Quit();
					std::exit(0);
				}
				break;
		}
	}
}

int main()
{
	init_sdl();
	init_ode();

	Ballo ballo;
	ballo.set_pos(vec(8, 12));
	
	Timer timer;
	
	while (true) {
		events();
		while (OVERSTEP > STEP) {
			step();
			OVERSTEP -= STEP;
		}
		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		ballo.draw();
		SDL_GL_SwapBuffers();
		OVERSTEP += timer.get_time_diff();
	}
}
