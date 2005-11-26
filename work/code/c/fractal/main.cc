#include <GL/gl.h>
#include <GL/glu.h>

#include <SDL/SDL.h>

#include <cstdlib>
#include <cmath>
#include <unistd.h>

typedef float num;

const int pix_width  = 640;
const int pix_height = 480;
const num screen_left = -2;
const num screen_right = 1;
const num screen_bottom = -1;
const num screen_top = 1;

num r = 1;

void draw_mandel();

SDL_Surface* screen;
void init_sdl() {
    SDL_Init(SDL_INIT_VIDEO);
    screen = SDL_SetVideoMode(pix_width, pix_height, 32, SDL_OPENGL);

    glMatrixMode(GL_PROJECTION);
        glLoadIdentity();
        gluOrtho2D(screen_left, screen_right, screen_bottom, screen_top);
    glMatrixMode(GL_MODELVIEW);
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
}

int main(int argc, char** argv) {
    init_sdl();

    num rs = -M_PI/2;
    glClear(GL_COLOR_BUFFER_BIT);
    for (;;) {
        r = 2*sin(rs);
        rs += 0.01;
        draw_mandel();
        SDL_GL_SwapBuffers();
        events();
    }
    
    quit();
}

int mandel_order(num cr, num ci, int limit) {
    int iters = 0;
    num zr = 0, zi = 0, rsq, isq;
    while (++iters < limit) {
        if ((isq = zi*zi) + (rsq=zr*zr) > 4) break;
        zi = ci + 2*zr*zi;
        zr = cr - isq + r*rsq;
    }
    if (iters == limit) return 0;
    else return iters;
}

void draw_mandel() {
    num rstep = (screen_right - screen_left) / pix_width;
    num istep = (screen_top - screen_bottom) / pix_height;

    glBegin(GL_POINTS);
    for (num r = screen_left; r <= screen_right; r += rstep) {
        for (num i = screen_bottom; i <= screen_top; i += istep) {
            int order = 30 * mandel_order(r, i, 200) % 256;
            glColor3ub(order, order, order);
            glVertex2d(r, i);
        }
    }
    glEnd();
}
