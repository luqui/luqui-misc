#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <cstdlib>
#include <ctime>
#include <vector>
#include <iostream>
#include <cmath>

const int ENERGY_TYPES = 1;
using std::vector;

float randrange(float min, float max) {
	return float(rand()) / RAND_MAX * (max - min) + min;
}

struct ParticleType {
	float bucket_size[ENERGY_TYPES];
};

struct Particle {
	Particle() 
		: type(0), buckets_buf1(), buckets_buf2(),
		  x(0), y(0)
	{ }
	ParticleType* type;
	float x, y;
	float buckets_buf1[ENERGY_TYPES];
	float buckets_buf2[ENERGY_TYPES];
};

typedef float (Particle::* buckets_t)[ENERGY_TYPES];

buckets_t buckets_f;
buckets_t buckets_b;

vector<Particle> particles;

void points()
{
	glBegin(GL_POINTS);
	for (int i = 0; i < particles.size(); i++) {
		for (int t = 0; t < ENERGY_TYPES; t++) {
			float& bv = (particles[i].*buckets_f)[t];
			float max = particles[i].type->bucket_size[t];
			
			glColor3f(1000*bv,fabs(1000*bv),-1000*bv);
			glVertex2f(particles[i].x, particles[i].y);
		}
	}
	glEnd();
}

void flow()
{
	for (int i = 0; i < particles.size(); i++) {
		for (int t = 0; t < ENERGY_TYPES; t++) {
			(particles[i].*buckets_b)[t] = (particles[i].*buckets_f)[t];
		}
	}
	
	glBegin(GL_LINES);
	for (int i = 0; i < particles.size(); i++) {
		for (int j = i+1; j < particles.size(); j++) {
			for (int t = 0; t < ENERGY_TYPES; t++) {
				float isq = ((particles[i].*buckets_f)[t] - particles[i].type->bucket_size[t]);
				float jsq = ((particles[j].*buckets_f)[t] - particles[j].type->bucket_size[t]);
		
				float distx = (particles[i].x - particles[j].x);
				float disty = (particles[i].y - particles[j].y);
				float dist2 = distx * distx + disty * disty;

				if (dist2 < 1) dist2 = 1;

				float flowij = (jsq - isq) / (120*dist2);
				
				(particles[i].*buckets_b)[t] += flowij;
				(particles[j].*buckets_b)[t] -= flowij;

				float draw = 10000*flowij;
				
				if (draw > 0.1) {
					glColor3f(draw, draw, draw);
					glVertex2f(particles[i].x, particles[i].y);
					glVertex2f(particles[j].x, particles[j].y);
				}
			}
		}
	}
	glEnd();
}

void init_sdl()
{
	SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER);
	SDL_SetVideoMode(800,600,0,SDL_OPENGL);

	glMatrixMode(GL_PROJECTION);
		glLoadIdentity();
		gluOrtho2D(0, 16, 0, 12);
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
}

void events()
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_KEYDOWN) 
			if (e.key.keysym.sym == SDLK_ESCAPE) 
				exit(0);
	}
	
	int x, y;
	SDL_GetMouseState(&x, &y);
	particles[0].x = x * float(16)/800;
	particles[0].y = (600-y) * float(12)/600;
	(particles[0].*buckets_f)[0] += 0.1;
	particles.back().type->bucket_size[0] += 0.1;
}

int main()
{
	init_sdl();
	srand(time(NULL));

	particles.resize(3000);

	ParticleType medium;
	medium.bucket_size[0] = 0;

	ParticleType sink;
	sink.bucket_size[0] = 0;

	particles[0].x = 16;
	particles[0].y = 12;
	particles[0].type = &medium;
	
	for (int i = 1; i < particles.size()-1; i++) {
		particles[i].x = randrange(0, 16);
		particles[i].y = randrange(0, 12);
		particles[i].type = &medium;
	}

	particles.back().x = 0;
	particles.back().y = 0;
	particles.back().type = &sink;

	buckets_f = &Particle::buckets_buf1;
	buckets_b = &Particle::buckets_buf2;
	
	while (true) {
		events();
		glClear(GL_COLOR_BUFFER_BIT);
		points();
		flow();
		SDL_GL_SwapBuffers();

		buckets_t btmp = buckets_f;
		buckets_f = buckets_b;
		buckets_b = btmp;
	}
}
