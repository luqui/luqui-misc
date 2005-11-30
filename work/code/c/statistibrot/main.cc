#include <GL/gl.h>
#include <GL/glu.h>

#include <SDL/SDL.h>

#include <cstdlib>
#include <cmath>
#include <ctime>
#include <iostream>
#include <unistd.h>

typedef float num;

const num SCRLEFT = -2;
const num SCRRIGHT = 1;
const num SCRBOT = -1;
const num SCRTOP = 1;

const int BUFFERSZ = 100000;

num perturb = 0;
num xbias = 0;
num ybias = 0;

struct Point {
    Point() { }
    Point(num x, num y) : x(x), y(y) { }
    num x, y;
};

Point outsidebuf[BUFFERSZ];
int outsidepts = 0;
Point insidebuf[BUFFERSZ];
int insidepts = 0;

SDL_Surface* screen;
void init_sdl() {
    SDL_Init(SDL_INIT_VIDEO);
    screen = SDL_SetVideoMode(800, 600, 32, SDL_OPENGL);

    glMatrixMode(GL_PROJECTION);
        glLoadIdentity();
        gluOrtho2D(SCRLEFT, SCRRIGHT, SCRBOT, SCRTOP);
    glMatrixMode(GL_MODELVIEW);
    
    glEnableClientState(GL_VERTEX_ARRAY);
}

void quit() {
    SDL_Quit();
    exit(0);
}

void events() {
    SDL_Event e;
    while (SDL_PollEvent(&e)) {
        switch (e.type) {
        case SDL_KEYDOWN:
            if (e.key.keysym.sym == SDLK_ESCAPE)
                quit();
            break;
        case SDL_QUIT:
            quit();
            break;
        }
    }

    Uint8* keys = SDL_GetKeyState(NULL);
    if (keys[SDLK_SPACE]) perturb += 0.002;
    else perturb = 0;

    if (keys[SDLK_UP])    ybias += 0.0002;
    if (keys[SDLK_DOWN])  ybias -= 0.0002;
    if (keys[SDLK_RIGHT]) xbias += 0.0002;
    if (keys[SDLK_LEFT])  xbias -= 0.0002;
    if (keys[SDLK_RETURN]) xbias = ybias = 0;
}

int mandel_order(num cr, num ci, int limit) {
    int iters = 0;
    num zr = 0, zi = 0, rsq, isq;
    while (++iters < limit) {
        if ((isq = zi*zi) + (rsq=zr*zr) > 4) break;
        zi = ci + 2*zr*zi;
        zr = cr - isq + rsq;
    }
    if (iters == limit) return 0;
    else return iters;
}

int fill_buffer() { 
    bool inpred = false, outpred = false;
    while (!(inpred && outpred)) {
        num x = drand48() * (SCRRIGHT - SCRLEFT) + SCRLEFT;
        num y = drand48() * (SCRTOP - SCRBOT) + SCRBOT;
        int ord = mandel_order(x,y,100);
        if (ord == 0) {
            if (insidepts < BUFFERSZ) {
                insidebuf[insidepts++] = Point(x,y);
            }
            else inpred = true;
        }
        else {
            if (outsidepts < BUFFERSZ) {
                outsidebuf[outsidepts++] = Point(x,y);
            }
            else outpred = true;
        }
    }
}

int min(int a, int b) {
    return a <= b ? a : b;
}

int max(int a, int b) {
    return a >= b ? a : b;
}

void pointselect(Point* in, Point* out) {
    num xpert = drand48() * perturb - perturb/2 + xbias;
    num ypert = drand48() * perturb - perturb/2 + ybias;
    Point avg((in->x + out->x) / 2 + xpert,
              (in->y + out->y) / 2 + ypert);
    int ord = mandel_order(avg.x, avg.y, 100);
    if (ord == 0) {
        *in = avg;
    }
    else {
        *out = avg;
    }
}

void evolve() {
    int inpt, outpt;
    
    int ptnum = inpt = outpt = lrand48() % max(insidepts, outsidepts);
    if (ptnum > insidepts)
        inpt = lrand48() % insidepts;
    if (ptnum > outsidepts)
        outpt = lrand48() % outsidepts;
    
    pointselect(&insidebuf[inpt], &outsidebuf[outpt]);
}

void draw() {
    glLoadIdentity();
    glColor3f(1,1,0);

    glVertexPointer(2, GL_FLOAT, sizeof(Point), outsidebuf);
    glDrawArrays(GL_POINTS, 0, outsidepts);

    glColor3f(1,0,0);

    glVertexPointer(2, GL_FLOAT, sizeof(Point), insidebuf);
    glDrawArrays(GL_POINTS, 0, insidepts);
}

int main(int argc, char** argv) {
    srand48(time(NULL));
    std::cout << "Filling point buffer...\n";
    fill_buffer();
    std::cout << "Done\n";
    
    init_sdl();

    int frames = 0;
    for (;;) {
        events();
        for (int i = 0; i < 1000; i++) { evolve(); }
        if (frames++ % 10 == 0) {
            SDL_GL_SwapBuffers();
            glClear(GL_COLOR_BUFFER_BIT);
        }
        draw();
    }
}
