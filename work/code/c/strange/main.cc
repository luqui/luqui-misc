#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <stdlib.h>
#include <map>
#include <cstdlib>
#include <cmath>

void init_sdl()
{
	SDL_Init(SDL_INIT_VIDEO);
	SDL_SetVideoMode(1280,1024,0,SDL_OPENGL | SDL_FULLSCREEN);
	SDL_ShowCursor(0);
	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	gluOrtho2D(-2,2,-1.5,1.5);
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
}

float P[10];
const float PM[10] = { 0, 1.5, 0, .5, 1.5,
					   0, 1.5, 0, .5, 1.5 };
const float PA[10] = { 2.0, 3.5, 3.5, 2.5, 4.7,
					   1.5, 3.5, 3.6, 2.5, 4.7 };
typedef std::map<SDLKey, int> paramcoord_t;
paramcoord_t PARAMX;
paramcoord_t PARAMY;

void reset() {
	for (int i = 0; i < 10; i++) {
		P[i] = PM[i];
	}
}

void events()
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_MOUSEMOTION) {
			Uint8* keys = SDL_GetKeyState(NULL);
			float dxf = float(e.motion.xrel)/640;
			float dyf = -float(e.motion.yrel)/512;

			for (paramcoord_t::iterator i = PARAMX.begin(); i != PARAMX.end(); ++i) {
				if (keys[i->first]) {
					P[i->second] += PA[i->second]*dxf;
				}
			}
			for (paramcoord_t::iterator i = PARAMY.begin(); i != PARAMY.end(); ++i) {
				if (keys[i->first]) {
					P[i->second] += PA[i->second]*dyf;
				}
			}
		}
		if (e.type == SDL_KEYDOWN) {
			if (e.key.keysym.sym == SDLK_ESCAPE) {
				SDL_Quit();
				exit(0);
			}
			if (e.key.keysym.sym == SDLK_r) {
				reset();
			}
		}
	}
}

float randrange(float a, float b)
{
	float r = float(rand()) / RAND_MAX;
	return a + (b - a) * r;
}

void drift(float amt)
{
	for (int i = 0; i < 10; i++) {
		P[i] += randrange(-amt, amt) * PA[i];
	}
}

void set_palette(float phase)
{
	glColor3f(
			0.5*sin(2*M_PI*phase)+0.5,
			0.5*cos(5*M_PI*phase)+0.5,
			0.5*sin(11*M_PI*phase)+0.5);
}

void draw_attractor(float x, float y)
{
	glPointSize(2.0);
	glBegin(GL_POINTS);
	for (int i = 0; i < 10000; i++) {
		float nx = P[0] - y*(P[1] * x*x + P[2] * x*y + P[3] * y*y + P[4] * x*x*y);
		float ny = P[5] + x*(P[6] * x*x + P[7] * x*y + P[8] * y*y + P[9] * y*y*x);
		x = nx;
		y = ny;
		set_palette(float(i)/10000);
		glVertex2f(x,y);
	}
	glEnd();
}

void draw()
{
	draw_attractor(0,0);
	/*
	glPointSize(4.0);
	glColor3f(1,1,1);
	glBegin(GL_POINTS);
	for (int i = 0; i < 5; i++) {
		glVertex2f((P[i]-PM[i])/PA[i], (P[i+5]-PM[i+5])/PA[i+5]);
	}
	glEnd();
	*/
}

int main()
{
	init_sdl();
	PARAMX[SDLK_a] = 0;
	PARAMY[SDLK_a] = 5;
	PARAMX[SDLK_s] = 1;
	PARAMY[SDLK_s] = 6;
	PARAMX[SDLK_d] = 2;
	PARAMY[SDLK_d] = 7;
	PARAMX[SDLK_f] = 3;
	PARAMY[SDLK_f] = 8;
	PARAMX[SDLK_g] = 4;
	PARAMY[SDLK_g] = 9;
	reset();
	while(true) {
		events();
		drift(0.0002);
		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
	}
	SDL_Quit();
}
