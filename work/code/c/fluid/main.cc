#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <cstdlib>
#include <list>
#include <cmath>

#include "config.h"
#include "vec.h"
#include "FluidGrid.h"
#include "Texture.h"

// Algorithms from "Real Time Fluid Dynamics for Games" by Jos Stam.

using std::list;

float DT = 0.01;

struct Particle {
	Particle(vec p) : p(p) { }
	vec p;
};

struct Player {
	Player(float sign, vec p) : sign(sign), p(p), store(0), storing(false), life(5), tex(0) { }
	float sign;  // positive or negative
	vec p;
	float store;
	bool storing;
	int life;
	vec blow;
	Texture* tex;
};

float WINTIMER = 0;
float PARTICLES_PENDING = 0;

const int INITIAL_PARTICLES = 10;
const float PARTICLE_RATE = 1;
const float CRITICAL = 2e-3;
const float PLSPEED = 20;
const float SPEEDSCALE = 0;
const float MAXSPEED = HUGE_VAL;
const float FLOWSPEED = 30;
const float PROPELSPEED = 10;
const float DENSPEED = 0;
const float EMPTYRATE = 1;
const float VISCOSITY = 1e-5;
const float DIFFUSION = 1e-5;
const float EATDIST = 1.414;
const float EATENERGY = 5;
const int DESTRAD = 5;
Player red(1,vec(10,H-11));
Player blue(-1,vec(W-11,10));
list<Particle> particles;

FluidDensityGrid* FIELD = 0;
FluidUtils::Bound BOUND;

float randrange(float min, float max) {
	return float(rand()) / RAND_MAX * (max - min) + min;
}

void step()
{
	if (WINTIMER == 0) {
		int win = 0;
		if (FIELD->get_density(red.p) < -CRITICAL) {
			red.life--;
			win = 1;
			red.store += 50;
		}
		else if (FIELD->get_density(blue.p) > CRITICAL) {
			blue.life--;
			win = -1;
			blue.store += 50;
		}
		if (win != 0) {
			WINTIMER = 5;
		}
	}
	WINTIMER -= DT;
	if (WINTIMER < 0) WINTIMER = 0;

	if (red.storing) red.store += DENSPEED*DT;
	else { 
		FIELD->add_density(red.p, EMPTYRATE*red.store + DENSPEED); 
		red.store -= EMPTYRATE*red.store*DT;
		if (red.store < 0) red.store = 0;
	}
	if (blue.storing) blue.store += DENSPEED*DT;
	else {
		FIELD->add_density(blue.p, -EMPTYRATE*blue.store - DENSPEED);
		blue.store -= EMPTYRATE*blue.store*DT;
		if (blue.store < 0) blue.store = 0;
	}
	FIELD->step_density(BOUND);
	FIELD->add_velocity(red.p, red.blow);
	FIELD->add_velocity(blue.p, blue.blow);
	FIELD->step_velocity(BOUND);

	for (list<Particle>::iterator i = particles.begin(); i != particles.end();) {
		i->p.x = clamp(i->p.x, 2, W-3);
		i->p.y = clamp(i->p.y, 2, H-3);
		vec v = FIELD->get_velocity(i->p);
		i->p += 60*DT*v;

		bool eaten = false;
		if ((i->p - red.p).norm2() < EATDIST*EATDIST) {
			red.store += EATENERGY;
			eaten = true;
		}
		if ((i->p - blue.p).norm2() < EATDIST*EATDIST) {
			blue.store += EATENERGY;
			eaten = true;
		}
		if (!eaten) {
			++i;
		}
		else {
			list<Particle>::iterator iprime = i;
			++iprime;
			particles.erase(i);
			i = iprime;
		}
	}

	PARTICLES_PENDING += PARTICLE_RATE * DT;
	while (PARTICLES_PENDING > 1) {
		PARTICLES_PENDING -= 1;
		particles.push_back(Particle(vec(randrange(2,W-3), randrange(2,H-3))));
	}
}

void set_color_at(int x, int y) {
	float d = 100*FIELD->get_density_direct(x,y);
	if (d > 0) {
		glColor3f(d, d/4, d/16);
	}
	else {
		glColor3f(-d/16, -d/4, -d);
	}
}

void draw()
{
	glBegin(GL_QUADS);
	for (int i = 0; i < W-1; i++) {
		for (int j = 0; j < H-1; j++) {
			set_color_at(i,j);
			glVertex2f(i,j);
			set_color_at(i+1,j);
			glVertex2f(i+1,j);
			set_color_at(i+1,j+1);
			glVertex2f(i+1,j+1);
			set_color_at(i,j+1);
			glVertex2f(i,j+1);
		}
	}
	glEnd();

	glPointSize(1.0);
	glBegin(GL_POINTS);
	glColor3f(0.8,0.8,0.8);
	for (list<Particle>::iterator i = particles.begin(); i != particles.end(); ++i) {
		glVertex2f(i->p.x, i->p.y);
	}
	glEnd();

	{
		TextureBinding b = red.tex->bind();
		glBegin(GL_QUADS);
			glTexCoord2f(0,1);  glVertex2f(red.p.x-3,red.p.y-3);
			glTexCoord2f(1,1);  glVertex2f(red.p.x+3,red.p.y-3);
			glTexCoord2f(1,0);  glVertex2f(red.p.x+3,red.p.y+3);
			glTexCoord2f(0,0);  glVertex2f(red.p.x-3,red.p.y+3);
		glEnd();
	}
	
	{
		TextureBinding b = blue.tex->bind();
		glBegin(GL_QUADS);
			glTexCoord2f(0,1);  glVertex2f(blue.p.x-3,blue.p.y-3);
			glTexCoord2f(1,1);  glVertex2f(blue.p.x+3,blue.p.y-3);
			glTexCoord2f(1,0);  glVertex2f(blue.p.x+3,blue.p.y+3);
			glTexCoord2f(0,0);  glVertex2f(blue.p.x-3,blue.p.y+3);
		glEnd();
	}
	
	glLineWidth(3.0);
	glBegin(GL_LINES);
		glColor3f(1,0,0);
		glVertex2f(3, H);
		glVertex2f(3+red.store, H);
		glColor3f(0,0,1);
		glVertex2f(W-4, H);
		glVertex2f(W-4-blue.store, H);
	glEnd();

	if (WINTIMER > 0) {
		glEnable(GL_BLEND);
		glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
		glBegin(GL_QUADS);
		glColor4f(0,0,0,WINTIMER/5);
		glVertex2f(0,0);
		glVertex2f(0,H);
		glVertex2f(W,H);
		glVertex2f(W,0);
		glEnd();
		glDisable(GL_BLEND);
	}
}

void init_sdl() 
{
	SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER);
	SDL_SetVideoMode(1440, 900, 0, SDL_OPENGL | SDL_FULLSCREEN);
	SDL_ShowCursor(0);

	glEnable(GL_TEXTURE_2D);
	
	glMatrixMode(GL_PROJECTION);
		glLoadIdentity();
		gluOrtho2D(0, W, 0, H+3);
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
}

float get_step() {
	static Uint32 last_time = SDL_GetTicks();
	Uint32 this_time = SDL_GetTicks();
	float timediff = float(this_time - last_time) / 1000;
	last_time = this_time;
	return timediff;
}

void events() 
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
			SDL_Quit();
			exit(0);
		}
	}

	Uint8* keys = SDL_GetKeyState(NULL);

	red.blow = vec();
	blue.blow = vec();
	if (keys[SDLK_a]) { red.p.x -= PLSPEED * DT; red.blow.x += PROPELSPEED; }
	if (keys[SDLK_d]) { red.p.x += PLSPEED * DT; red.blow.x -= PROPELSPEED; }
	if (keys[SDLK_s]) { red.p.y -= PLSPEED * DT; red.blow.y += PROPELSPEED; }
	if (keys[SDLK_w]) { red.p.y += PLSPEED * DT; red.blow.y -= PROPELSPEED; }

	if (keys[SDLK_LEFT])  { blue.p.x -= PLSPEED * DT; blue.blow.x += PROPELSPEED; }
	if (keys[SDLK_RIGHT]) { blue.p.x += PLSPEED * DT; blue.blow.x -= PROPELSPEED; }
	if (keys[SDLK_DOWN])  { blue.p.y -= PLSPEED * DT; blue.blow.y += PROPELSPEED; }
	if (keys[SDLK_UP])    { blue.p.y += PLSPEED * DT; blue.blow.y -= PROPELSPEED; }

	if (keys[SDLK_h])  red.blow.x -= FLOWSPEED;
	if (keys[SDLK_k])  red.blow.x += FLOWSPEED;
	if (keys[SDLK_j])  red.blow.y -= FLOWSPEED;
	if (keys[SDLK_u])  red.blow.y += FLOWSPEED;

	if (keys[SDLK_KP4]) blue.blow.x -= FLOWSPEED;
	if (keys[SDLK_KP6]) blue.blow.x += FLOWSPEED;
	if (keys[SDLK_KP5]) blue.blow.y -= FLOWSPEED;
	if (keys[SDLK_KP8]) blue.blow.y += FLOWSPEED;

	red.p.x  = clamp(red.p.x,  2, W-3);
	red.p.y  = clamp(red.p.y,  2, H-3);
	blue.p.x = clamp(blue.p.x, 2, W-3);
	blue.p.y = clamp(blue.p.y, 2, H-3);
}

void reset()
{
	delete FIELD;
	FIELD = new FluidDensityGrid(vec(0,0), vec(W,H), DIFFUSION, VISCOSITY);

	red = Player(1,vec(10,H-11));
	red.tex = load_texture("firefly.png");
	blue = Player(-1,vec(W-11,10));
	blue.tex = load_texture("firefly.png");

	WINTIMER = 0;
	
	for (int i = 1; i < W-1; i++) {
		BOUND[i][0]  .full   = true;
		BOUND[i][0]  .normal = vec(0,1);
		BOUND[i][H-1].full   = true;
		BOUND[i][H-1].normal = vec(0,-1);
	}
	for (int j = 1; j < H-1; j++) {
		BOUND[0]  [j].full   = true;
		BOUND[0]  [j].normal = vec(1,0);
		BOUND[W-1][j].full   = true;
		BOUND[W-1][j].normal = vec(-1,0);
	}
	BOUND[0][0].full = BOUND[0][H-1].full = BOUND[W-1][0].full = BOUND[W-1][H-1].full = true;
	BOUND[0][0]    .normal = ~vec(1,1);
	BOUND[0][H-1]  .normal = ~vec(1,-1);
	BOUND[W-1][0]  .normal = ~vec(-1,1);
	BOUND[W-1][H-1].normal = ~vec(-1,-1);
	
	particles.clear();
	for (int i = 0; i < INITIAL_PARTICLES; i++) {
		particles.push_back(Particle(vec(randrange(1,W-2), randrange(1,H-2))));
	}
}

int main() 
{
	init_sdl();

	reset();

	get_step();
	DT = 0.01;
	while (true) {
		events();
		step();
		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
		DT = get_step();

		if (red.life <= 0 || blue.life <= 0) {
			reset();
		}
	}
}
