#include <iostream>

#include "common.h"
#include "player.h"
#include "geometry.h"
#include "objects.h"
#include "level.h"

num STEP = 1/60.0;
num OVERSTEP = 0;

int P1_SCORE = 0;
int P2_SCORE = 0;

void setup_gfx() {
    SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER | SDL_INIT_NOPARACHUTE);
    SDL_SetVideoMode(PIXEL_WIDTH, PIXEL_HEIGHT, 24, 
                     SDL_OPENGL | (SDL_FULLSCREEN * FULLSCREEN)) >= 0
        || DIE("Couldn't set video mode: " + SDL_GetError());
    
    SDL_ShowCursor(0);
}

num get_time_diff() {
    static Uint32 prev = SDL_GetTicks();
    Uint32 time = SDL_GetTicks();
    num ret = num(time - prev) / 1000.0;
    prev = time;
    return ret;
}

int main(int argc, char** argv) {
    setup_gfx();

    string level = argc == 2 ? argv[1] : "levels/walls.lvl";
    
    LEVEL = new Level;
    LEVEL->load_level(level);
    MOUSE_FOCUS = LEVEL->player;

    num overstep = 0;
    
    while (true) {
        events();
        LEVEL->step();
        overstep -= STEP;

        if (LEVEL->frozen()) {
            bool restart = true;
            if (LEVEL->p1->dead() && LEVEL->p2->dead()) ;
            else if (LEVEL->p1->dead()) P2_SCORE++;
            else if (LEVEL->p2->dead()) P1_SCORE++;
            else restart = false;

            if (restart) {
                delete LEVEL;
                LEVEL = new Level;
                LEVEL->load_level(level);
                MOUSE_FOCUS = LEVEL->player;
            }
        }

        // avoid degenerate behavior for expensive step()s.
        if (overstep > STEP) overstep = STEP;
        while (overstep <= STEP) {
            if (!LEVEL->frozen()) OVERSTEP = overstep; else OVERSTEP = 0;
            glClear(GL_COLOR_BUFFER_BIT);
            glLoadIdentity();
            LEVEL->draw();
            SDL_GL_SwapBuffers();
            overstep += get_time_diff();
        }
    }

    delete LEVEL;
    quit();
}
