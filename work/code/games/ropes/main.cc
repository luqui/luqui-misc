#include <iostream>

#include "common.h"
#include "player.h"
#include "geometry.h"
#include "objects.h"

dWorldID WORLD;
num STEP = 1/30.0;
num OVERSTEP = 0;

void setup_gfx() {
    SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER);
    SDL_SetVideoMode(PIXEL_WIDTH, PIXEL_HEIGHT, 24, 
                     SDL_OPENGL | (SDL_FULLSCREEN * FULLSCREEN)) >= 0
        || DIE("Couldn't set video mode: " + SDL_GetError());
    
    glMatrixMode(GL_PROJECTION);
        glLoadIdentity();
        gluOrtho2D(SCREEN_LEFT, SCREEN_RIGHT, SCREEN_BOTTOM, SCREEN_TOP);
    glMatrixMode(GL_MODELVIEW);

    SDL_ShowCursor(0);
}

num get_time_diff() {
    static Uint32 prev = SDL_GetTicks();
    Uint32 time = SDL_GetTicks();
    num ret = num(time - prev) / 1000.0;
    prev = time;
    return ret;
}

void setup_physics() {
    WORLD = dWorldCreate();
    COLLIDE_SPACE = dSimpleSpaceCreate(0);
    COLLIDE_JOINTS = dJointGroupCreate(0);
    dWorldSetGravity(WORLD, 0, -1, 0);
}

void step() {
    events();
    collide();
    dWorldQuickStep(WORLD, STEP);
    dJointGroupEmpty(COLLIDE_JOINTS);
}

int main() {
    setup_gfx();
    setup_physics();

    Wall w(vec(0,0), vec(16,1));
    
    Player* p = new Player(vec(8,6));
    MOUSE_FOCUS = p;

    while (true) {
        step();
        p->step();
        OVERSTEP -= STEP;

        // avoid degenerate behavior for expensive step()s.
        if (OVERSTEP > STEP) OVERSTEP = STEP;
        while (OVERSTEP <= STEP) {
            glClear(GL_COLOR_BUFFER_BIT);
            glLoadIdentity();
            p->draw();
            w.draw();
            SDL_GL_SwapBuffers();
            OVERSTEP += get_time_diff();
        }
    }

    delete p;
    quit();
}
