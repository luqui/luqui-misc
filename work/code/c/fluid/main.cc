#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <cstdlib>
#include <list>
#include <cmath>

// Algorithms from "Real Time Fluid Dynamics for Games" by Jos Stam.

using std::list;

const int W = 160;
const int H = 120;

typedef float Scr[W][H];

Scr U, V, U_BACK, V_BACK;
Scr DENSITY, DENSITY_BACK;
Scr DSOURCE, USOURCE, VSOURCE;
const float DT = 0.01;

struct Particle {
	Particle(float x, float y) : x(x), y(y) { }
	float x, y;
};

struct Player {
	Player(float sign, float x, float y) : sign(sign), x(x), y(y), score(0), store(0), storing(false) { }
	float sign;  // positive or negative
	float x, y;
	float store;
	bool storing;
	int score;
};

const float CRITICAL = 1.0/100.0;
const float PLSPEED = 35;
const float SPEEDSCALE = PLSPEED/CRITICAL;
const float FLOWSPEED = 300;
const float DENSPEED = 1;
const float EMPTYRATE = 3;
const int DESTRAD = 5;
Player red(1,10,H-11);
Player blue(-1,W-11,10);
list<Particle> particles;

float randrange(float min, float max) {
	return float(rand()) / RAND_MAX * (max - min) + min;
}

float clamp(float x, float lo, float hi)
{
	if (x <= lo) return lo;
	if (x >= hi) return hi;
	return x;
}

void set_bnd(int ty, Scr x) {
	for (int i = 1; i < W-1; i++) {
		x[i][0]   = ty == 2 ? -x[i][1]   : x[i][1];
		x[i][H-1] = ty == 2 ? -x[i][H-2] : x[i][H-2];
	}
	for (int j = 1; j < H-1; j++) {
		x[0][j]   = ty == 1 ? -x[1][j]   : x[1][j];
		x[W-1][j] = ty == 1 ? -x[W-2][j] : x[W-2][j];
	}
	x[0][0]     = 0.5*(x[1][0]   + x[0][1]);
	x[0][H-1]   = 0.5*(x[1][H-1] + x[0][H-2]);
	x[W-1][0]   = 0.5*(x[W-2][0] + x[W-1][1]);
	x[W-1][H-1] = 0.5*(x[W-2][H-1] + x[W-1][H-2]);
}

void add_source(Scr x, Scr s) 
{
	for (int i = 0; i < W; i++) {
		for (int j = 0; j < H; j++) {
			x[i][j] += DT*s[i][j];
		}
	}
}

void diffuse(int ty, Scr x, Scr x0, float diff)
{
	float da = DT * diff * (W-2)*(H-2);
	
	for (int k = 0; k < 20; k++) {  // XXX 20?
		for (int i = 1; i < W-1; i++) {
			for (int j = 1; j < H-1; j++) {
				x[i][j] = (x0[i][j] + da * (x[i-1][j] + x[i+1][j]
							              + x[i][j-1] + x[i][j+1])) / (1+4*da);
			}
		}
		set_bnd(ty, x);
	}
}

void advect(int ty, Scr d, Scr d0, Scr u, Scr v)
{
	for (int i = 1; i < W-1; i++) {
		for (int j = 1; j < H-1; j++) {
			float x = i - DT*W*u[i][j];
			float y = j - DT*H*v[i][j];
			int i0 = int(clamp(x, 0.5, W-1.5));
			int i1 = i0+1;
			int j0 = int(clamp(y, 0.5, H-1.5));
			int j1 = j0+1;
			float s1 = x - i0; float s0 = 1 - s1;
			float t1 = y - j0; float t0 = 1 - t1;
			d[i][j] = s0*(t0*d0[i0][j0] + t1*d0[i0][j1])
				    + s1*(t0*d0[i1][j0] + t1*d0[i1][j1]);
		}
	}
	set_bnd(ty, d);
}

void project(Scr u, Scr v, Scr p, Scr div)
{
	float hx = 1.0/W;
	float hy = 1.0/H;

	for (int i = 1; i < W-1; i++) {
		for (int j = 1; j < H-1; j++) {
			div[i][j] = -0.5*( hx*(u[i+1][j] - u[i-1][j])
					         + hy*(v[i][j+1] - v[i][j-1]));
			p[i][j] = 0;
		}
	}

	set_bnd(0, div);
	set_bnd(0, p);

	for (int k = 0; k < 20; k++) {   // XXX 20?
		for (int i = 1; i < W-1; i++) {
			for (int j = 1; j < H-1; j++) {
				p[i][j] = (div[i][j] + p[i-1][j] + p[i+1][j]
									 + p[i][j-1] + p[i][j+1]) / 4.0;
			}
		}
		set_bnd(0, p);
	}

	for (int i = 1; i < W-1; i++) {
		for (int j = 1; j < H-1; j++) {
			u[i][j] -= 0.5 * (p[i+1][j] - p[i-1][j]) / hx;
			v[i][j] -= 0.5 * (p[i][j+1] - p[i][j-1]) / hy;
		}
	}
	set_bnd(1, u);
	set_bnd(2, v);
}

template<class T>
void swap(T& x, T& y) 
{
	T tmp = x;
	x = y;
	y = tmp;
}

void density_step(Scr x, Scr x0, Scr u, Scr v, float diff)
{
	diffuse(0, x0, x, diff);
	advect(0, x, x0, u, v);
}

void velocity_step(Scr u, Scr v, Scr u0, Scr v0, float visc) {
	diffuse(1, u0, u, visc);
	diffuse(2, v0, v, visc);
	project(u0, v0, u, v);
	advect(1, u, u0, u0, v0);
	advect(2, v, v0, u0, v0);
	project(u, v, u0, v0);
}

void step()
{
	int redx = int(red.x);  int redy = int(red.y);
	int blux = int(blue.x); int bluy = int(blue.y);

	int win = 0;
	int winx, winy;
	if (DENSITY[redx][redy] < -CRITICAL) {
		blue.score++;
		DSOURCE[redx][redy] = 1;
		win = 1;
		winx = redx; winy = redy;
	}
	else if (DENSITY[blux][bluy] > CRITICAL) {
		red.score++;
		DSOURCE[blux][bluy] = -1;
		win = -1;
		winx = blux; winy = bluy;
	}
	if (win != 0) {
		for (int i = 0; i < W; i++) {
			for (int j = 0; j <= H; j++) {
				if ((i - red.x)*(i - red.x) + (j - red.y)*(j - red.y)
				  < (i - blue.x)*(i - blue.x) + (j - blue.y)*(j - blue.y)) {
					DENSITY[i][j] = fabs(DENSITY[i][j]);
				}
				else {
					DENSITY[i][j] = -fabs(DENSITY[i][j]);
				}
			}
		}

		for (int i = 0; i < W; i++) {
			for (int j = 0; j < H; j++) {
				USOURCE[i][j] = VSOURCE[i][j] = 0;
			}
		}
	}


	//add_source(DENSITY, DSOURCE);
	if (red.storing) red.store += DENSPEED*DT;
	else { 
		DENSITY[redx][redy] += EMPTYRATE*red.store*DT + DENSPEED*DT; 
		red.store -= EMPTYRATE*red.store*DT;
	}
	if (blue.storing) blue.store += DENSPEED*DT;
	else {
		DENSITY[blux][bluy] -= EMPTYRATE*blue.store*DT + DENSPEED*DT;
		blue.store -= EMPTYRATE*blue.store*DT;
	}
	add_source(U, USOURCE);
	add_source(V, VSOURCE);
	density_step(DENSITY, DENSITY_BACK, U, V, 1e-5);
	velocity_step(U, V, U_BACK, V_BACK, 0.001);

	for (list<Particle>::iterator i = particles.begin(); i != particles.end(); ++i) {
		i->x = clamp(i->x, 2, W-3);
		i->y = clamp(i->y, 2, H-3);
		int ix = int(i->x);
		int iy = int(i->y);
		float u = U[ix][iy];
		float v = V[ix][iy];
		i->x += 60*DT*u;
		i->y += 60*DT*v;
	}
}

void draw()
{
	glPointSize(4.0);
	glBegin(GL_POINTS);
	for (int i = 0; i < W; i++) {
		for (int j = 0; j < H; j++) {
			float d = DENSITY[i][j] / CRITICAL;
			float s = USOURCE[i][j] * USOURCE[i][j] + VSOURCE[i][j] * VSOURCE[i][j] + fabs(DSOURCE[i][j]);
			float g = fabs(d) > 1 ? 0.5 : 0;
			glColor3f(d,g + (s > 0 ? 0.7 : 0),-d);
			glVertex2f(i,j);
		}
	}
	glEnd();

	glPointSize(1.0);
	glBegin(GL_POINTS);
	glColor3f(0.8,0.8,0.8);
	for (list<Particle>::iterator i = particles.begin(); i != particles.end(); ++i) {
		glVertex2f(i->x, i->y);
	}
	glEnd();

	glPointSize(6.0);
	glBegin(GL_POINTS);
		glColor3f(1,0.7,0.7);
		glVertex2f(red.x,red.y);
		for (int i = 0; i < red.score; i++) {
			glVertex2f(3*i+3, H+1);
		}
		glColor3f(0.7,0.7,1);
		glVertex2f(blue.x,blue.y);
		for (int i = 0; i < blue.score; i++) {
			glVertex2f(W-3*i-4, H+1);
		}
	glEnd();

	glLineWidth(3.0);
	glBegin(GL_LINES);
		glColor3f(1,0,0);
		glVertex2f(3, H);
		glVertex2f(3+red.store, H);
		glColor3f(0,0,1);
		glVertex2f(W-4, H);
		glVertex2f(W-4-blue.store, H);
	glEnd();
}

void init_sdl() 
{
	SDL_Init(SDL_INIT_VIDEO);
	SDL_SetVideoMode(640, 480, 0, SDL_OPENGL | SDL_FULLSCREEN);
	SDL_ShowCursor(0);
	glMatrixMode(GL_PROJECTION);
		glLoadIdentity();
		gluOrtho2D(0, W, 0, H+3);
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
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

	int redx = int(red.x);
	int redy = int(red.y);
	
	int blux = int(blue.x);
	int bluy = int(blue.y);

	float rspeed = PLSPEED + SPEEDSCALE*DENSITY[redx][redy];
	rspeed = clamp(rspeed, 0, 2*PLSPEED);
	float bspeed = PLSPEED - SPEEDSCALE*DENSITY[blux][bluy];
	bspeed = clamp(bspeed, 0, 2*PLSPEED);

	if (keys[SDLK_a]) red.x -= rspeed * DT;
	if (keys[SDLK_d]) red.x += rspeed * DT;
	if (keys[SDLK_s]) red.y -= rspeed * DT;
	if (keys[SDLK_w]) red.y += rspeed * DT;

	if (keys[SDLK_LEFT])  blue.x -= bspeed * DT;
	if (keys[SDLK_RIGHT]) blue.x += bspeed * DT;
	if (keys[SDLK_DOWN])  blue.y -= bspeed * DT;
	if (keys[SDLK_UP])    blue.y += bspeed * DT;

	if (keys[SDLK_g])   USOURCE[redx][redy] -= FLOWSPEED * DT;
	if (keys[SDLK_j])   USOURCE[redx][redy] += FLOWSPEED * DT;
	if (keys[SDLK_h])   VSOURCE[redx][redy] -= FLOWSPEED * DT;
	if (keys[SDLK_y])   VSOURCE[redx][redy] += FLOWSPEED * DT;

	if (keys[SDLK_KP4]) USOURCE[blux][bluy] -= FLOWSPEED * DT;
	if (keys[SDLK_KP6]) USOURCE[blux][bluy] += FLOWSPEED * DT;
	if (keys[SDLK_KP5]) VSOURCE[blux][bluy] -= FLOWSPEED * DT;
	if (keys[SDLK_KP8]) VSOURCE[blux][bluy] += FLOWSPEED * DT;

	if (keys[SDLK_b]) {
		for (int i = redx - DESTRAD; i <= redx + DESTRAD; i++) {
			for (int j = redy - DESTRAD; j <= redy + DESTRAD; j++) {
				if (0 <= i && i < W && 0 <= j && j < H) {
					USOURCE[i][j] = VSOURCE[i][j] = 0;
				}
			}
		}
	}

	if (keys[SDLK_KP1]) {
		for (int i = blux - DESTRAD; i <= blux + DESTRAD; i++) {
			for (int j = bluy - DESTRAD; j <= bluy + DESTRAD; j++) {
				if (0 <= i && i < W && 0 <= j && j < H) {
					USOURCE[i][j] = VSOURCE[i][j] = 0;
				}
			}
		}
	}

	red.storing = keys[SDLK_n];
	blue.storing = keys[SDLK_KP2];

	red.x = clamp(red.x, 2, W-3);
	red.y = clamp(red.y, 2, H-3);
	blue.x = clamp(blue.x, 2, W-3);
	blue.y = clamp(blue.y, 2, H-3);
}

int main() 
{
	init_sdl();

	const int nclears = 9;
	Scr* clear[nclears] = { &U, &V, &U_BACK, &V_BACK, &DENSITY, &DENSITY_BACK, &DSOURCE, &USOURCE, &VSOURCE };
	for (int c = 0; c < nclears; c++) {
		for (int i = 0; i < W; i++) {
			for (int j = 0; j < H; j++) {
				(*clear[c])[i][j] = 0;
			}
		}
	}

	for (int i = 0; i < 5000; i++) {
		particles.push_back(Particle(randrange(1,W-2), randrange(1,H-2)));
	}

	DSOURCE[12][H-13] = 1;
	DSOURCE[W-13][12] = -1;

	while (true) {
		events();
		step();
		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
	}
}
