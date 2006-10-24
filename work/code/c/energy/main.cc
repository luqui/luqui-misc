#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <soy/vec2.h>
#include <soy/vec3.h>
#include <soy/init.h>
#include <soy/Viewport.h>
#include <soy/Timer.h>
#include <soy/util.h>

#include <cmath>
#include <list>
#include <iostream>

using std::list;

struct Cell {
	vec3 color;
	vec3 color_rate;
	vec3 voltage;
};

const double STEP = 1/30.0;
const int STEPS = 1;
const double DT = STEP/STEPS;
const double TIMESCALE = 1;
const double DAMPING = 0.05;

const int WIDTH  = 150;
const int HEIGHT = 150;

bool SHOW_VOLTAGE = false;
bool SHOW_ENERGY = false;

typedef Cell grid_t[WIDTH][HEIGHT];

SoyInit INIT;
Viewport VIEW(vec2((WIDTH-1) / 2.0, (HEIGHT-1) / 2.0), vec2(WIDTH, HEIGHT));

grid_t FRONT;
grid_t BACK;

void init_sdl() {
	INIT.set_fullscreen();
	INIT.init();
	VIEW.activate();
}

void events() {
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_KEYDOWN) {
			switch(e.key.keysym.sym) {
			case SDLK_ESCAPE:
				SDL_Quit();
				exit(0);
				break;
			case SDLK_v:
				SHOW_VOLTAGE = !SHOW_VOLTAGE;
				break;
			case SDLK_e:
				SHOW_ENERGY = !SHOW_ENERGY;
				break;
			default:
				break;
			}
		}
	}

	int mx, my;
	Uint8 button = SDL_GetMouseState(&mx, &my);
	
	vec2 mpos = coord_convert(INIT.pixel_view(), VIEW, vec2(mx, my));
	mx = int(mpos.x);  my = int(mpos.y);
	for (int i = mx - 1; i <= mx + 1; i++) {
		for (int j = my - 1; j <= my + 1; j++) {
			if (button & SDL_BUTTON(1)) FRONT[mx][my].color.x += STEP;
			if (button & SDL_BUTTON(2)) FRONT[mx][my].color.y += STEP;
			if (button & SDL_BUTTON(3)) FRONT[mx][my].color.z += STEP;
		}
	}
}

vec3 potential(vec3 in) {
	static const double normscale = 1.0/sqrt(3);
	double r = in.norm() * normscale;
	vec3 pos = vec3(r,r,r) - in;
	vec3 neg = -vec3(r,r,r) - in;

	vec3 overvolt = vec3(
			in.x > 1 ? 1 - in.x : in.x < 0 ? -in.x : 0,
			in.y > 1 ? 1 - in.y : in.y < 0 ? -in.y : 0,
			in.z > 1 ? 1 - in.z : in.z < 0 ? -in.z : 0);

	if (pos.norm2() <= neg.norm2()) {
		return pos + overvolt;
	}
	else {
		return neg + overvolt;
	}
}

void advect(int id, int jd, int is, int js, double scale) {
	vec3 field = scale * DT * (BACK[id][jd].color_rate - BACK[is][js].color_rate);
	
	FRONT[id][jd].color += field;
	FRONT[is][js].color -= field;
}

void set_boundary()
{
	for (int i = 0; i < WIDTH; i++) {
		FRONT[i][0].color        = vec3();
		FRONT[i][HEIGHT-1].color = vec3();
	}
	
	for (int j = 0; j < HEIGHT; j++) {
		FRONT[0][j].color       = vec3();
		FRONT[WIDTH-1][j].color = vec3();
	}
}

void step() {
	set_boundary();

	// Compute voltages
	for (int i = 1; i < WIDTH - 1; i++) {
		for (int j = 1; j < HEIGHT - 1; j++) {
			FRONT[i][j].voltage = potential(FRONT[i][j].color);
			FRONT[i][j].color_rate += 0.2 * DT * (FRONT[i][j].voltage - DAMPING * FRONT[i][j].color_rate);
		}
	}
	
	// Copy front to back
	memcpy(BACK, FRONT, sizeof(BACK));

	// Move charges around
	const double diag = 1/sqrt(2);
	for (int i = 1; i < WIDTH - 1; i++) {
		for (int j = 1; j < HEIGHT - 1; j++) {
			advect(i,j, i-1, j  , 1);
			advect(i,j, i,   j-1, 1);
			advect(i,j, i+1, j  , 1);
			advect(i,j, i,   j+1, 1);
			
			advect(i,j, i+1, j+1, diag);
			advect(i,j, i+1, j-1, diag);
			advect(i,j, i-1, j+1, diag);
			advect(i,j, i-1, j-1, diag);
		}
	}
}

void set_color(const Cell& cell) {
	if (SHOW_VOLTAGE) {
		glColor3f(fabs(cell.voltage.x), fabs(cell.voltage.y), fabs(cell.voltage.z));
	}
	else if (SHOW_ENERGY) {
		glColor3f(cell.color.x, cell.color.y, cell.color.z);
	}
}

void draw() {
	if (SHOW_VOLTAGE || SHOW_ENERGY) {
		glBegin(GL_QUADS);
		for (int i = 0; i < WIDTH - 1; i++) {
			for (int j = 0; j < HEIGHT - 1; j++) {
				set_color(FRONT[i][j]);
				glVertex2f     (i, j);
				set_color(FRONT[i+1][j]);
				glVertex2f     (i+1, j);
				set_color(FRONT[i+1][j+1]);
				glVertex2f     (i+1, j+1);
				set_color(FRONT[i][j+1]);
				glVertex2f     (i, j+1);
			}
		}
		glEnd();
	}
}

int main() {
	init_sdl();

	FrameRateLockTimer timer(STEP/TIMESCALE);
	
	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < HEIGHT; j++) {
			FRONT[i][j].color = vec3(0.5, 0.5, 0.5);
		}
	}

	while (true) {
		events();
		for (int i = 0; i < STEPS; i++) {
			step();
		}
		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
		timer.lock();
	}
}
