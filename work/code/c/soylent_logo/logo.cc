#include <SDL/SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <cstdlib>
#include <ctime>
#include <cmath>

using namespace std;

const float LEFT = -4, RIGHT = 4, BOTTOM = -3, TOP = 3;

const int DEP_W = 160;
const int DEP_H = 128;

const float STEP = 0.004;

float depbuf1[DEP_W][DEP_H];
float depbuf2[DEP_W][DEP_H];

float (*depression)[DEP_W][DEP_H];
float (*depression_back)[DEP_W][DEP_H];

const int PARTICLES = 30000;
struct Particle {
    Particle() { }
    Particle(float x, float y, float vx = 0, float vy = 0)
        : x(x), y(y), vx(vx), vy(vy)
    { }
    float x, y, vx, vy;
};
Particle particles[PARTICLES];

int FIXED_POINTS = 0;
int fixed[DEP_W*DEP_H][2];

void load_fixed_points()
{
    SDL_Surface* surf = SDL_LoadBMP("logo.bmp");
    SDL_LockSurface(surf);
    int bpp = surf->format->BytesPerPixel;
    char* pixels = (char*)surf->pixels;
    for (int i = 0; i < surf->w; i++) {
        for (int j = 0; j < surf->h; j++) {
            if (pixels[j*surf->pitch + bpp*i]) {
                fixed[FIXED_POINTS][0] = i;
                fixed[FIXED_POINTS][1] = DEP_H-j;
                FIXED_POINTS++;
            }
        }
    }
    SDL_UnlockSurface(surf);
    SDL_FreeSurface(surf);
}

int init_gl()
{
    SDL_Init(SDL_INIT_VIDEO);
    SDL_SetVideoMode(1400, 900, 0, SDL_OPENGL | SDL_FULLSCREEN);
    SDL_ShowCursor(0);

    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluOrtho2D(2*LEFT,2*RIGHT,2*BOTTOM,2*TOP);
    glMatrixMode(GL_MODELVIEW);
    glLoadIdentity();
}

float randrange(float min, float max) {
    return (float(rand()) / RAND_MAX) * (max - min) + min;
}

bool in_range(int x, int y) {
    return x >= 0 && x < DEP_W && y >= 0 && y < DEP_H;
}

int x2px(float x) {
    return int(((x - LEFT) / (RIGHT - LEFT)) * DEP_W);
}

int y2py(float y) {
    return int(((y - BOTTOM) / (TOP - BOTTOM)) * DEP_H);
}

void integrate_depression()
{
    for (int i = 1; i < DEP_W-1; i++) {
        for (int j = 1; j < DEP_H-1; j++) {
            float sum = 0; int pts = 0;
            for (int di = -1; di <= 1; di++) {
                for (int dj = -1; dj <= 1; dj++) {
                    sum += (*depression)[i+di][j+dj];
                    pts++;
                }
            }
            if (pts) {
                (*depression_back)[i][j] = sum / pts;
            }
            else {
                (*depression_back)[i][j] = (*depression)[i][j];
            }
        }
    }
    float (*temp)[DEP_W][DEP_H] = depression;
    depression = depression_back;
    depression_back = temp;
}

void integrate_particles()
{
    for (int i = 0; i < PARTICLES; i++) {
        Particle& p = particles[i];
        int px = x2px(p.x);
        int py = y2py(p.y);
        float dx = 0, dy = 0;
        for (int di = -1; di <= 1; di++) {
            for (int dj = -1; dj <= 1; dj++) {
                if (in_range(px+di,py+dj)) {
                    dx += di * (*depression)[px+di][py+dj];
                    dy += dj * (*depression)[px+di][py+dj];
                }
            }
        }
        float dep = (*depression)[px][py];
        p.vx += (dx - 2*(1 - dep) * p.vx) * STEP;
        p.vy += (dy - 2*(1 - dep) * p.vy) * STEP;
        p.x += p.vx * STEP;
        p.y += p.vy * STEP;

        if (p.x < LEFT)   { p.vx = -p.vx; p.x += 2 * p.vx * STEP; }
        if (p.x > RIGHT)  { p.vx = -p.vx; p.x += 2 * p.vx * STEP; }
        if (p.y < BOTTOM) { p.vy = -p.vy; p.y += 2 * p.vy * STEP; }
        if (p.y > TOP)    { p.vy = -p.vy; p.y += 2 * p.vy * STEP; }
    }
}

void draw()
{
    glClear(GL_COLOR_BUFFER_BIT);
    glColor3f(1,1,1);
    glPointSize(2.0);
    glBegin(GL_POINTS);
    for (int i = 0; i < PARTICLES; i++) {
        int px = x2px(particles[i].x);
        int py = y2py(particles[i].y);
        float v = particles[i].vx * particles[i].vy;
        float dep = (*depression)[px][py];
        float r = 2*particles[i].vx;
        float g = 2*particles[i].vy;
        float b = fabs(1-v);
        glColor3f(r, g, b);
        glVertex2f(particles[i].x, particles[i].y);
    }
    glEnd();
    SDL_GL_SwapBuffers();
}

void events()
{
    SDL_Event e;
    while (SDL_PollEvent(&e)) {
        if (e.type == SDL_QUIT 
         || e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
            SDL_Quit();
            exit(0);
        }
    }
}

int main()
{
    srand(time(NULL));
    
    for (int i = 0; i < DEP_W; i++)
        for (int j = 0; j < DEP_H; j++)
            depbuf1[i][j] = depbuf2[i][j] = 0;

    depression = &depbuf1;
    depression_back = &depbuf2;
    
    for (int i = 0; i < PARTICLES; i++)
        particles[i] = Particle(randrange(-4,4), randrange(-3,3), randrange(-12,12), randrange(-12,12));

    init_gl();

    load_fixed_points();

    for (int i = 0; i < FIXED_POINTS; i++) {
        (*depression)[fixed[i][0]][fixed[i][1]] = 1;
    }
    integrate_depression();

    while (true) {
        events();
        
        integrate_particles();
        draw();
    }
}
