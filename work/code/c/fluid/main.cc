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
	add_source(DENSITY, DSOURCE);
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
			float d = 500*DENSITY[i][j];
			float s = USOURCE[i][j] * USOURCE[i][j] + VSOURCE[i][j] * VSOURCE[i][j] + fabs(DSOURCE[i][j]);
			glColor3f(d,s > 0 ? 0.5 : 0,-d);
			glVertex2f(i,j);
		}
	}
	glEnd();

	/*
	glColor3f(0,0.2,0.8);
	glBegin(GL_LINES);
	for (int i = 1; i < W-1; i += 3) {
		for (int j = 1; j < H-1; j += 3) {
			float vx = 20*U[i][j];
			float vy = 20*V[i][j];
			glVertex2f(i,j);
			glVertex2f(i+vx, j+vy);
		}
	}
	glEnd();
	*/

	glPointSize(1.0);
	glBegin(GL_POINTS);
	glColor3f(0.8,0.8,0.8);
	for (list<Particle>::iterator i = particles.begin(); i != particles.end(); ++i) {
		glVertex2f(i->x, i->y);
	}
	glEnd();
}

void init_sdl() 
{
	SDL_Init(SDL_INIT_VIDEO);
	SDL_SetVideoMode(640, 480, 0, SDL_OPENGL | SDL_FULLSCREEN);
	glMatrixMode(GL_PROJECTION);
		glLoadIdentity();
		gluOrtho2D(0, W, 0, H);
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
	int x, y;
	SDL_GetMouseState(&x, &y);
	int fx = x/(640/W);
	int fy = (480-y)/(480/H);

	if (fx > 0 && fx < W-1 && fy > 0 && fy < H-1) {
		Uint8* keys = SDL_GetKeyState(NULL);
		if (keys[SDLK_a]) USOURCE[fx][fy] -= 3;
		if (keys[SDLK_d]) USOURCE[fx][fy] += 3;
		if (keys[SDLK_s]) VSOURCE[fx][fy] -= 3;
		if (keys[SDLK_w]) VSOURCE[fx][fy] += 3;
		if (keys[SDLK_z]) {
			for (int i = -1; i <= 1; i++) {
				for (int j = -1; j <= 1; j++) {
					USOURCE[fx+i][fy+j] = VSOURCE[fx+i][fy+j] = DSOURCE[fx][fy] = 0;
				}
			}
		}
		if (keys[SDLK_x]) DSOURCE[fx][fy] += 0.01;
		if (keys[SDLK_c]) DSOURCE[fx][fy] -= 0.01;
	}
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

	while (true) {
		events();
		step();
		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
	}
}
