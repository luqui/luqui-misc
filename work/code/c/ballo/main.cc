#include "config.h"
#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <cstdlib>
#include <cmath>
#include <ode/ode.h>
#include "vec.h"
#include "Timer.h"

dWorldID WORLD;
num OVERSTEP = 0;
const num STEP = 0.01;

class Body
{
public:
	Body() 
		: body_(dBodyCreate(WORLD)),
		  plane2d_(dJointCreatePlane2D(WORLD, 0))
	{
		dJointAttach(plane2d_, body_, 0);
	}

	~Body() {
		dJointDestroy(plane2d_);
		dBodyDestroy(body_);
	}

	void set_pos(vec posin) {
		dBodySetPosition(body_, posin.x, posin.y, 0);
	}

	vec pos() const { 
		const dReal* posout = dBodyGetPosition(body_);
		return vec(posout[0], posout[1]);
	}

	void set_vel(vec velin) {
		dBodySetLinearVel(body_, velin.x, velin.y, 0);
	}

	vec vel() const {
		const dReal* velout = dBodyGetLinearVel(body_);
		return vec(velout[0], velout[1]);
	}

	vec drawing_pos() const {
		return pos() + OVERSTEP * vel();
	}
	
protected:
	dBodyID body_;
	dJointID plane2d_;
};

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

void init_ode()
{
	WORLD = dWorldCreate();
	dWorldSetGravity(WORLD, 0, -1, 0);
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
