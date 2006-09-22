#include <soy/init.h>
#include <soy/Timer.h>
#include <soy/vec2.h>
#include <soy/Viewport.h>
#include <soy/util.h>
#include <cstdlib>
#include <GL/gl.h>
#include <GL/glu.h>
#include <list>

const double MOUSE_ATTRACTION = 10;
const double DAMPING = 0.035;
const double POWER = 1;
double ENEMY_GROW_RATE = 0;
const double ENEMY_GROW_RATE_RATE = 0.001;
double ENEMY_SPAWN_RATE = 0.05;
const double ENEMY_SPAWN_RATE_RATE = 0.0002;
bool MOUSE_DOWN = false;
const int HISTORY_SIZE = 10;

double DT = 1/30.0;
SoyInit INIT;

Viewport VIEW(vec2(48, 36), vec2(96, 72));
vec2 MOUSE;

struct Particle {
	typedef std::list<vec2> history_t;
	Particle(vec2 pos, vec2 vel) : pos(pos), vel(vel) { }
	vec2 pos, vel;
	history_t history;
};

struct Enemy {
	Enemy(vec2 pos, vec2 vel, double radius) : pos(pos), vel(vel), radius(radius), particles(0) { }
	vec2 pos, vel;
	double radius;
	int particles;
};

typedef std::list<Particle> particles_t;
particles_t PARTICLES;
typedef std::list<Enemy> enemies_t;
enemies_t ENEMIES;

void init_sdl() 
{
	INIT.set_fullscreen();
	INIT.init();
	VIEW.activate();
}

void draw() 
{
	glLoadIdentity();
	for (particles_t::iterator i = PARTICLES.begin(); i != PARTICLES.end(); ++i) {
		glBegin(GL_LINE_STRIP);
			glColor3f(1,1,1);
			glVertex2f(i->pos.x, i->pos.y);
			float col = 1;
			for (Particle::history_t::iterator j = i->history.begin(); j != i->history.end(); ++j) {
				glColor3f(col,10*col,col);
				glVertex2f(j->x, j->y);
				col /= 1.5;
			}
		glEnd();
	}

	for (enemies_t::iterator i = ENEMIES.begin(); i != ENEMIES.end(); ++i) {
		glColor3f(i->particles/36.0,i->particles/6.0,1);
		glBegin(GL_TRIANGLE_FAN);
			glVertex2f(i->pos.x, i->pos.y);
			for (int n = 0; n <= 24; n++) {
				float theta = 2*M_PI*n/24;
				glVertex2f(i->pos.x + i->radius*cos(theta), i->pos.y + i->radius*sin(theta));
			}
		glEnd();
	}

	vec2 center(48,36);
	glColor3f(0.4,0,0);
	glBegin(GL_LINE_STRIP);
		for (int n = 0; n <= 48; n++) {
			float theta = 2*M_PI*n/48;
			glVertex2f(center.x + 36*cos(theta), center.y + 36*sin(theta));
		}
	glEnd();
}

void events()
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
			exit(0);
		}
	}

	int x, y;
	Uint8 buts = SDL_GetMouseState(&x, &y);
	MOUSE = coord_convert(INIT.pixel_view(), VIEW, vec2(x,y));
	MOUSE_DOWN = !!(buts & SDL_BUTTON(1));
}

void step()
{
	for (particles_t::iterator i = PARTICLES.begin(); i != PARTICLES.end();) {
		bool killparticle = false;

		vec2 accel;
		if (MOUSE_DOWN) {
			double dist = (MOUSE - i->pos).norm();
			if (dist < 0.05) dist = 0.05;
			accel = MOUSE_ATTRACTION * ~(MOUSE - i->pos);
		}
		
		for (particles_t::iterator j = PARTICLES.begin(); j != PARTICLES.end(); ++j) {
			if (i == j) continue;
			double dist = (i->pos - j->pos).norm();
			double coef = -1/dist + 1/(dist*dist);
			if (coef > 100) coef = 100;
			if (coef < -100) coef = -100;
			accel += coef * ~(i->pos - j->pos);
		}

		const vec2 center(48,36);
		double outside = (center - i->pos).norm();
		if (outside > 36) {
			accel += 0.05 * (center - i->pos) * (outside - 36);
		}

		for (enemies_t::iterator j = ENEMIES.begin(); j != ENEMIES.end();) {
			bool kill = false;
			if ((i->pos - j->pos).norm() < j->radius) {
				double newr2 = j->radius*j->radius - POWER;
				if (newr2 < 0) { kill = true; }
				else           { j->radius = sqrt(newr2); }
				j->particles++;
				killparticle = true;
			}

			if (kill) {
				for (int n = 0; n < j->particles; n++) {
					vec2 offs(randrange(-1,1), randrange(-1,1));
					PARTICLES.push_back(Particle(j->pos + offs, 10*offs));
				}
				enemies_t::iterator k = j;
				++j;
				ENEMIES.erase(k);
			}
			else {
				++j;
			}
		}

		accel -= DAMPING * i->vel.norm() * i->vel;
		i->vel += DT * accel;

		if (killparticle) {
			particles_t::iterator j = i;
			++i;
			PARTICLES.erase(j);
		}
		else {
			++i;
		}
	}
		
	for (enemies_t::iterator i = ENEMIES.begin(); i != ENEMIES.end(); ++i) {
		vec2 accel;
		const vec2 center(48,36);
		double outside = (center - i->pos).norm();
		if (outside > 36) {
			accel += 0.05 * (center - i->pos) * (outside - 36);
		}

		i->radius = sqrt(i->radius*i->radius + ENEMY_GROW_RATE*DT);
		i->vel += DT * accel;
		i->pos += i->vel;
	}
	
	for (particles_t::iterator i = PARTICLES.begin(); i != PARTICLES.end(); ++i) {
		i->history.push_front(i->pos);
		if (i->history.size() > HISTORY_SIZE) {
			i->history.pop_back();
		}
		i->pos += DT * i->vel;
	}

	ENEMY_GROW_RATE += ENEMY_GROW_RATE_RATE*DT;
	ENEMY_SPAWN_RATE += ENEMY_GROW_RATE_RATE*DT;
}

int main()
{
	FrameRateLockTimer timer(DT);
	init_sdl();
	for (int i = 0; i < 2; i++) {
		PARTICLES.push_back(Particle(vec2(randrange(32,64),randrange(24,48)), vec2(0,0)));
	}
	float spawn_timer = 3.0/20.0;
	while (true) {
		events();
		step();
		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
		
		spawn_timer -= ENEMY_SPAWN_RATE*DT;
		while (spawn_timer < 0) {
			double r = ENEMY_SPAWN_RATE;
			ENEMIES.push_back(Enemy(vec2(randrange(16,80),randrange(12,60)), vec2(randrange(-r,r),randrange(-r,r)), 1.1));
			ENEMIES.back().particles++;
			spawn_timer += 1;
		}
		
		timer.lock();
	}
}
