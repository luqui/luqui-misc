#include <soy/init.h>
#include <soy/Timer.h>
#include <soy/vec2.h>
#include <soy/Viewport.h>
#include <soy/util.h>
#include <cstdlib>
#include <GL/gl.h>
#include <GL/glu.h>
#include <list>

const double MOUSE_ATTRACTION = 20;
const double HISTORY_TIME = 1/30.0;
const double ATTRACTION = 4;
const double SPREAD_REPULSION = 10;
const double DAMPING = 0.015;
const double ENEMY_DAMPING = 0.1;
const double POWER = 1;
const double DIVIDE_TIME = 8;
const double DIVIDE_VAR = 1;
const double MASS_PER_PARTICLE = 0.9;
const double PARTICLE_MOMENTUM = 0.8;
const int MAX_INCUBATE = 10;
double ENEMY_GROW_RATE = 0;
double INITIAL_SIZE = 1;
const double ENEMY_INIT_RATE = 0.01;
const double ENEMY_GROW_RATE_RATE = 0.003;
double ENEMY_SPAWN_RATE = 0.05;
const double ENEMY_SPAWN_RATE_RATE = 0.001;
bool MOUSE_DOWN = false;
bool RIGHT_MOUSE_DOWN = false;
const int HISTORY_SIZE = 15;
double TIME = 0;

double DT = 1/30.0;
SoyInit INIT;

Viewport VIEW(vec2(48, 36), vec2(96, 72));
vec2 MOUSE;

struct Particle {
	typedef std::list<vec2> history_t;
	Particle(vec2 pos, vec2 vel) : pos(pos), vel(vel), last_history(0) { }
	vec2 pos, vel;
	double last_history;
	history_t history;
};

struct Enemy {
	Enemy(vec2 pos, vec2 vel, double radius) : pos(pos), vel(vel), radius(radius), particles(0), init_particles(0) { }
	vec2 pos, vel;
	double radius;
	int particles;
	int init_particles;
	std::list<double> incubate;
};

typedef std::list<Particle> particles_t;
particles_t PARTICLES;
int NPARTICLES = 0;
typedef std::list<Enemy> enemies_t;
enemies_t ENEMIES;

void init_sdl() 
{
	INIT.set_fullscreen();
	INIT.init();
	VIEW.activate();
}

void draw_score(int score) {
	const int colors = 4;
	const int color[colors][3] = {
		{ 0, 1, 0 },
		{ 0, 0, 1 },
		{ 1, 0, 0 },
		{ 1, 1, 1 } };
	const int value[colors] = { 100, 25, 5, 1 };

	int counter = 0;
	int row = 0;
	int col = 0;

	while (score > 0) {
		while (score < value[counter]) { counter++; }
		score -= value[counter];
		
		glColor3f(color[counter][0], color[counter][1], color[counter][2]);
		
		while (col > 10) {
			row++;
			col -= 10;
		}

		glBegin(GL_QUADS);
			glVertex2f(2*col+1, 2*row+1);
			glVertex2f(2*col+2, 2*row+1);
			glVertex2f(2*col+2, 2*row+2);
			glVertex2f(2*col+1, 2*row+2);
		glEnd();

		col++;
	}
}

void draw() 
{
	glLoadIdentity();
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glLineWidth(2.0);
	for (particles_t::iterator i = PARTICLES.begin(); i != PARTICLES.end(); ++i) {
		glBegin(GL_LINE_STRIP);
			glColor4f(1,1,1,0.75);
			glVertex2f(i->pos.x, i->pos.y);
			float col = 1;
			float ratio = exp(4.5 / HISTORY_SIZE);
			for (Particle::history_t::iterator j = i->history.begin(); j != i->history.end(); ++j) {
				glColor4f(col,1,col,0.75*col);
				glVertex2f(j->x, j->y);
				col /= ratio;
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

	draw_score(NPARTICLES);
}

void events()
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
			exit(0);
		}
		if (e.type == SDL_MOUSEBUTTONDOWN && e.button.button == SDL_BUTTON_LEFT) {
			for (particles_t::iterator i = PARTICLES.begin(); i != PARTICLES.end(); ++i) {
				double scale = ~i->vel * ~(MOUSE - i->pos);
				if (scale < 0) scale = 0;
				i->vel = scale * i->vel.norm() * ~(MOUSE - i->pos);
			}
		}
	}

	int x, y;
	Uint8 buts = SDL_GetMouseState(&x, &y);
	MOUSE = coord_convert(INIT.pixel_view(), VIEW, vec2(x,y));
	MOUSE_DOWN = !!(buts & SDL_BUTTON(1));
	RIGHT_MOUSE_DOWN = !!(buts & SDL_BUTTON(3));
}

void step()
{
	TIME += DT;
	INITIAL_SIZE += ENEMY_INIT_RATE * DT;

	for (particles_t::iterator i = PARTICLES.begin(); i != PARTICLES.end();) {
		bool killparticle = false;

		vec2 accel;
		accel = MOUSE_ATTRACTION * ~(MOUSE - i->pos);
		
		for (particles_t::iterator j = PARTICLES.begin(); j != PARTICLES.end(); ++j) {
			if (i == j) continue;
			double dist1 = 1/(i->pos - j->pos).norm();
			double coef = dist1*dist1*dist1 - dist1*dist1;
			if (coef > 100) coef = 100;
			if (coef < -100) coef = -100;
			if (RIGHT_MOUSE_DOWN) coef *= -10/ATTRACTION;
			accel += ATTRACTION * coef * (i->pos - j->pos)*dist1;
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
				j->init_particles++;
				if (j->incubate.size() < MAX_INCUBATE) {
					j->incubate.push_back(TIME + DIVIDE_TIME + randrange(-DIVIDE_VAR, DIVIDE_VAR));
				}
				killparticle = true;
			}

			if (kill) {
				for (int n = 0; n < j->particles; n++) {
					vec2 offs(randrange(-1,1), randrange(-1,1));
					PARTICLES.push_back(Particle(j->pos + offs, 10*offs));
				}
				//NPARTICLES += j->particles - j->init_particles;
				NPARTICLES++;
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
			accel += 0.35 * (center - i->pos) * (outside - 36);
		}

		while (i->incubate.size() && TIME >= i->incubate.front()) {
			i->incubate.pop_front();
			i->particles++;
			i->radius = sqrt(i->radius*i->radius + MASS_PER_PARTICLE);
			if (i->incubate.size() < MAX_INCUBATE) {
				i->incubate.push_back(TIME + DIVIDE_TIME + randrange(-DIVIDE_VAR, DIVIDE_VAR));
			}
		}

		i->radius = sqrt(i->radius*i->radius + ENEMY_GROW_RATE*DT);
		i->vel += DT * accel;
		i->pos += DT * i->vel;
	}
	
	for (particles_t::iterator i = PARTICLES.begin(); i != PARTICLES.end(); ++i) {
		if (TIME >= i->last_history + HISTORY_TIME) {
			i->history.push_front(i->pos);
			if (i->history.size() > HISTORY_SIZE) {
				i->history.pop_back();
			}
			i->last_history = TIME;
		}
		i->pos += DT * i->vel;
	}

	ENEMY_GROW_RATE += ENEMY_GROW_RATE_RATE*DT;
	ENEMY_SPAWN_RATE += ENEMY_SPAWN_RATE_RATE*DT;
}

int main()
{
	Timer timer;
	srand(time(NULL));
	init_sdl();
	for (int i = 0; i < 3; i++) {
		PARTICLES.push_back(Particle(vec2(randrange(32,64),randrange(24,48)), vec2(0,0)));
	}
	float spawn_timer = 3.0/20.0;
	timer.init();
	while (true) {
		events();
		step();
		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
		
		spawn_timer -= ENEMY_SPAWN_RATE*DT;
		while (spawn_timer < 0) {
			double r = 30 * ENEMY_SPAWN_RATE;
			vec2 speed(randrange(-r,r),randrange(-r,r));
			ENEMIES.push_back(Enemy(vec2(randrange(16,80),randrange(12,60)), speed, sqrt(INITIAL_SIZE)));
			spawn_timer += 1;
		}
		
		DT = timer.get_time_diff();
		if (DT > 1/15.0) DT = 1/15.0;
	}
}
