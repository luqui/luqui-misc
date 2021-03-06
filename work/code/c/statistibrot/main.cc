#include <GL/gl.h>
#include <GL/glu.h>

#include <SDL/SDL.h>

#include <cstdlib>
#include <cmath>
#include <ctime>
#include <iostream>

// The plotting forms.  Have exactly one of these
// uncommented at all times.  Try different ones.

// #define X3PLUS1
// #define X3PLUSX
// #define X3MINUSX
// #define X3
// #define X3PLUSX2PLUSXPLUS1
// #define JULIAR
#define JULIARI


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
        : x(x), y(y), z(z)
    { }
    num x, y, z;
    num nx, ny, nz;
};

void set_normals(Point* a, Point* b) {
    num vabx = b->x - a->x;
    num vaby = b->y - a->y;
    num vabz = b->z - a->z;
    
    num norm = sqrt(vabx*vabx + vaby*vaby + vabz*vabz);
    
    vabx /= norm;
    vaby /= norm;
    vabz /= norm;

    b->nx = vabx;
    b->ny = vaby;
    b->nz = vabz;
    a->nx = vabx;
    a->ny = vaby;
    a->nz = vabz;
}

Point outsidebuf[BUFFERSZ];
int outsidepts = 0;
Point insidebuf[BUFFERSZ];
int insidepts = 0;

const int max_iters = 400;
const num max_bound = 100;

num viewx = 4, viewy = 4, viewz = 4;

void set_lights() {
    num ambient[] = { 0.5, 0.5, 0.5, 1.0 };
    glLightfv(GL_LIGHT0, GL_AMBIENT, ambient);

    num diffuse[] = { 1.0, 1.0, 1.0, 1.0 };
    glLightfv(GL_LIGHT0, GL_DIFFUSE, diffuse);
    
    num position[4];
    position[0] = viewx;  position[1] = viewy;  position[2] = viewz;  position[3] = 1.0;
    glLightfv(GL_LIGHT0, GL_POSITION, position);
}


double floatrand() {
    return double(rand()) / double(RAND_MAX);
}

SDL_Surface* screen;
void init_sdl() {
    SDL_Init(SDL_INIT_VIDEO);
    screen = SDL_SetVideoMode(800, 600, 32, SDL_OPENGL);

    glMatrixMode(GL_PROJECTION);
        glLoadIdentity();
        gluPerspective(45.0, 800.0/600.0, 0.01, 50);
    glMatrixMode(GL_MODELVIEW);
    
    glEnableClientState(GL_VERTEX_ARRAY);
    glEnableClientState(GL_NORMAL_ARRAY);

    glEnable(GL_DEPTH_TEST);
    glDepthFunc(GL_LEQUAL);

    glEnable(GL_LIGHTING);
    glEnable(GL_LIGHT0);
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
            if (fabs(a*a + b*b + c*c) > max_bound)
                return iters;
        
#if defined(X3PLUS1)
        // ax^2 + bx + c   (mod x^3 + 1)
        ap =  2*a*c + b*b + d;
        bp =  2*b*c - a*a + e;
        cp = -2*a*b + c*c + f;
#elif defined(X3PLUSX)
        // ax^2 + bx + c   (mod x^3 + x)
        ap =  2*a*c + b*b - a*a + d;
        bp =  2*b*c - 2*a*b     + e;
        cp =  c*c               + f;
#elif defined(X3MINUSX)
        // ax^2 + bx + c   (mod x^3 - x)
        ap = a*a + b*b + 2*a*c + d;
        bp = 2*b*c + 2*a*b     + e;
        cp = c*c               + f;
#elif defined(X3)
        // ax^2 + bx + c   (mod x^3)
        ap =  2*a*c + b*b + d;
        bp =  2*b*c       + e;
        cp =          c*c + f;
#elif defined(X3PLUSX2PLUSXPLUS1)
        // ax^2 + bx + c   (mod x^3 + x^2 + x + 1)
        ap = 2*a*c + b*b - 2*a*b + d;
        bp = 2*b*c - 2*a*b       + e;
        cp = c*c - 2*a*b + a*a   + f;
#elif defined(JULIAR)
        // ax + b (mod x^2 + 1)  (standard mandelbrot)
        // initial a is determined by the parameter f.
        if (iters == 1) a = f;
        ap = a*a - b*b           + d;
        bp = 2*a*b               + e;
        cp = 0;
#elif defined(JULIARI)
        // ax + b (mod x^2 + 1)  (standard mandelbrot)
        // initial a and b are determined by the parameter f
        if (iters == 1) a = b = f;
        ap = a*a - b*b           + d;
        bp = 2*a*b               + e;
        cp = 0;
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
        
        num x = floatrand() * (SCRRIGHT - SCRLEFT) + SCRLEFT;
        num y = floatrand() * (SCRTOP - SCRBOT) + SCRBOT;
        num z = floatrand() * (SCRFRONT - SCRBACK) + SCRBACK;
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
    for (int i = 0; i < BUFFERSZ; i++) {
        set_normals(&insidebuf[i], &outsidebuf[i]);
    }
}

int min(int a, int b) {
    return a <= b ? a : b;
}

int max(int a, int b) {
    return a >= b ? a : b;
}

// Take two points, one inside and one outside the set, 
// and caculate their average.  If the average is in the
// set, then move the point that was formerly in the set
// to the average.  If the average is not in the set,
// then move the point that was formerly not in the set
// to the average.  This makes the two points exponentially
// converge on the boundary of the set.
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
    set_normals(in, out);
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
    
    set_lights();
    glColor3f(1,1,1);
    glVertexPointer(3, GL_FLOAT, sizeof(Point), &outsidebuf[0].x);
    glNormalPointer(GL_FLOAT, sizeof(Point), &outsidebuf[0].nx);
    glDrawArrays(GL_POINTS, 0, outsidepts);
}

int main(int argc, char** argv) {
    srand(time(NULL));
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
