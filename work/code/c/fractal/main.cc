#include <GL/gl.h>
#include <GL/glu.h>

#include <SDL/SDL.h>

#include <cstdlib>
#include <cmath>
#include <unistd.h>

typedef float num;

const int buf_width  = 200;
const int buf_height = 200;
const num screen_left = -2;
const num screen_right = 1;
const num screen_bottom = -1;
const num screen_top = 1;

num buffer[buf_width][buf_height];

typedef num buf_t[buf_width][buf_height];

void fill_buffer(buf_t, num, num, num, num);
void draw_buffer(buf_t, num, num, num, num);

num camerax = 0;
num cameray = 0;
num cameraz = -1;
num camerastep = 0.05;

SDL_Surface* screen;
void init_sdl() {
    SDL_Init(SDL_INIT_VIDEO);
    screen = SDL_SetVideoMode(800, 600, 32, SDL_OPENGL);

    glMatrixMode(GL_PROJECTION);
        glLoadIdentity();
        gluPerspective(45.0, 800.0/600.0, 0.1, 100);
    glMatrixMode(GL_MODELVIEW);

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
        }
    }

    Uint8* keys = SDL_GetKeyState(NULL);
    if (keys[SDLK_a]) camerax -= camerastep;
    if (keys[SDLK_d]) camerax += camerastep;
    if (keys[SDLK_w]) cameraz += camerastep;
    if (keys[SDLK_s]) cameraz -= camerastep;
}

int main(int argc, char** argv) {
    init_sdl();

    fill_buffer(buffer, screen_left, screen_right, screen_bottom, screen_top);
    for (;;) {
        glLoadIdentity();
        gluLookAt(camerax, cameray, cameraz,
                  0, 0, 10,
                  0, 1, 0);
        glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
        draw_buffer(buffer, screen_left, screen_right, screen_bottom, screen_top);
        SDL_GL_SwapBuffers();
        events();
    }
    
    quit();
}

num mandel_order(num cr, num ci, int limit) {
    int iters = 0;
    num zr = 0, zi = 0, rsq, isq;
    while (++iters < limit) {
        if ((isq = zi*zi) + (rsq=zr*zr) > 4) break;
        zi = ci + 2*zr*zi;
        zr = cr - isq + rsq;
    }
    if (iters == limit) return 300;
    else return iters;
}

void fill_buffer(buf_t buffer, num left, num right, num bottom, num top)
{
    num rstep = (right - left) / buf_width;
    num istep = (top - bottom) / buf_height;

    int rind, iind;
    num r, i;
    
    for (r = left, rind = 0; rind < buf_width; r += rstep, rind++) {
        for (i = bottom, iind = 0; iind < buf_height; i += istep, iind++) {
            buffer[rind][iind] = log(mandel_order(r, i, 200) + 0.5);
        }
    }
}

void itercolor(num iters) { 
    if (iters > log(200.0)) {
        glColor3d(0,0,0);
    }
    else {
        glColor3d(sin(10*iters), cos(10*iters), 1);
    }
}

void draw_buffer(buf_t buffer, num left, num right, num bottom, num top)
{
    num rstep = (right - left) / buf_width;
    num istep = (top - bottom) / buf_height;
    
    int rind, iind;
    num r, i;

    for (r = left, rind = 0; rind < buf_width-1; r += rstep, rind++) {
        for (i = bottom, iind = 0; iind < buf_height-1; i += istep, iind++) {
            glBegin(GL_QUADS);
                itercolor(buffer[rind][iind]);
                glVertex3d(r, i, buffer[rind][iind]);
                itercolor(buffer[rind][iind]);
                glVertex3d(r + rstep, i, buffer[rind][iind]);
                itercolor(buffer[rind][iind]);
                glVertex3d(r + rstep, i + istep, buffer[rind][iind]);
                itercolor(buffer[rind][iind]);
                glVertex3d(r, i + istep, buffer[rind][iind]);
            glEnd();
        }
    }
}
