#include <GL/gl.h>
#include <GL/glu.h>

#include <SDL/SDL.h>

#include <cstdlib>
#include <cmath>
#include <ctime>
#include <iostream>
#include <unistd.h>

// #define X3PLUS1
// #define X3PLUSX
// #define X3MINUSX
// #define X3
#define X3PLUSX2PLUSXPLUS1


typedef float num;

const num SCRLEFT = -2;
const num SCRRIGHT = 2;
const num SCRBOT = -2;
const num SCRTOP = 2;
const num SCRBACK = -2;
const num SCRFRONT = 2;
const int BUFFERSZ = 1000000;

struct Point {
    Point() { }
    Point(num x, num y, num z)
        : x(x), y(y), z(z),
          r(fabs(x)/2), g(fabs(y)/2), b(fabs(z)/2)
    { }
    num x, y, z;
    num r, g, b;
};

Point outsidebuf[BUFFERSZ];
int outsidepts = 0;
Point insidebuf[BUFFERSZ];
int insidepts = 0;

const int max_iters = 400;
const num max_bound = 100;

num viewx = 4, viewy = 4, viewz = 4;

SDL_Surface* screen;
void init_sdl() {
    SDL_Init(SDL_INIT_VIDEO);
    screen = SDL_SetVideoMode(800, 600, 32, SDL_OPENGL);

    glMatrixMode(GL_PROJECTION);
        glLoadIdentity();
        gluPerspective(45.0, 800.0/600.0, 0.01, 50);
    glMatrixMode(GL_MODELVIEW);
    
    glEnableClientState(GL_VERTEX_ARRAY);
    glEnableClientState(GL_COLOR_ARRAY);

    glEnable(GL_DEPTH_TEST);
    glDepthFunc(GL_LEQUAL);
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
    if (keys[SDLK_LEFT])  viewx -= 0.06;
    if (keys[SDLK_RIGHT]) viewx += 0.06;
    if (keys[SDLK_DOWN])  viewy -= 0.06;
    if (keys[SDLK_UP])    viewy += 0.06;
    if (keys[SDLK_z])     viewz -= 0.06;
    if (keys[SDLK_a])     viewz += 0.06;
}

int mandel_order(num d, num e, num f, int limit) {
    int iters = 0;

    num ap = 0, bp = 0, cp = 0;
    while (++iters < limit) {
        num a = ap, b = bp, c = cp;
        
        if (iters % 10 == 0)
            if (fabs(a*a*a - b*b*b + c*c*c + 3*a*b*c) > max_bound)
                return iters;
        
#if defined(X3PLUS1)
        ap =  2*a*c + b*b + d;
        bp =  2*b*c - a*a + e;
        cp = -2*a*b + c*c + f;
#elif defined(X3PLUSX)
        ap =  2*a*c + b*b - a*a + d;
        bp =  2*b*c - 2*a*b     + e;
        cp =  c*c               + f;
#elif defined(X3MINUSX)
        ap = a*a + b*b + 2*a*c + d;
        bp = 2*b*c + 2*a*b     + e;
        cp = c*c               + f;
#elif defined(X3)
        ap =  2*a*c + b*b + d;
        bp =  2*b*c       + e;
        cp =          c*c + f;
#elif defined(X3PLUSX2PLUSXPLUS1)
        ap = 2*a*c + b*b - 2*a*b + d;
        bp = 2*b*c - 2*a*b       + e;
        cp = c*c - 2*a*b + a*a   + f;
#endif
    }
    return 0;
}

int fill_buffer() { 
    std::cout << "Filling point buffer...\n";
    while (!(insidepts == BUFFERSZ && outsidepts == BUFFERSZ)) {
        if ((insidepts + outsidepts) % (2*BUFFERSZ/100) == 0) {
            num complete = 100 * num(insidepts + outsidepts) / num(2*BUFFERSZ);
            std::cout << "\e[0G\e[2K" << complete << "%";
            std::cout.flush();
        }
        
        num x = drand48() * (SCRRIGHT - SCRLEFT) + SCRLEFT;
        num y = drand48() * (SCRTOP - SCRBOT) + SCRBOT;
        num z = drand48() * (SCRFRONT - SCRBACK) + SCRBACK;
        int ord = mandel_order(x,y,z,max_iters);
        if (ord == 0) {
            if (insidepts < BUFFERSZ) {
                insidebuf[insidepts++] = Point(x,y,z);
            }
        }
        else {
            if (outsidepts < BUFFERSZ) {
                outsidebuf[outsidepts++] = Point(x,y,z);
            }
        }
    }
    std::cout << "\n";
    std::cout << "Done\n";
}

int min(int a, int b) {
    return a <= b ? a : b;
}

int max(int a, int b) {
    return a >= b ? a : b;
}

void pointselect(Point* in, Point* out) {
    Point avg((in->x + out->x) / 2,
              (in->y + out->y) / 2,
              (in->z + out->z) / 2);
    int ord = mandel_order(avg.x, avg.y, avg.z, max_iters);
    if (ord == 0) {
        *in = avg;
    }
    else {
        *out = avg;
    }
}

void evolve() {
    static int ctr = 0;
    int inpt, outpt;
    
    int ptnum = inpt = outpt = ctr++;
    ctr %= min(insidepts, outsidepts);
    
    pointselect(&insidebuf[inpt], &outsidebuf[outpt]);
}

void draw() {
    glLoadIdentity();
    gluLookAt(viewx, viewy, viewz,
              0, 0, 0,
              0, 1, 0);
    glPointSize(4.0);
    
    glVertexPointer(3, GL_FLOAT, sizeof(Point), &outsidebuf[0].x);
    glColorPointer(3, GL_FLOAT, sizeof(Point), &outsidebuf[0].r);
    glDrawArrays(GL_POINTS, 0, outsidepts);
}

int main(int argc, char** argv) {
    srand48(time(NULL));
    fill_buffer();
    
    init_sdl();

    int frames = 0;
    for (;;) {
        events();
        for (int i = 0; i < 10000; i++) { evolve(); }
        glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
        draw();
        SDL_GL_SwapBuffers();
    }
}
