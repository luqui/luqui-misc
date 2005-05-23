#include "setup.h"

dWorldID world;

const float force = 10.0;

int main(int argc, char** argv)
{
    init_gfx();
    init_2d();
    
    world = dWorldCreate();

    dBodyID ball = dBodyCreate(world);
    dBodySetPosition(ball, 0, 0, 0);

    for (;;) {
        Uint8* chars = SDL_GetKeyState(NULL);

        if (chars[SDLK_LEFT]) {
            dBodyAddForce(ball, -force, 0, 0);
        }
        if (chars[SDLK_RIGHT]) {
            dBodyAddForce(ball, +force, 0, 0);
        }
        if (chars[SDLK_UP]) {
            dBodyAddForce(ball, 0, +force, 0);
        }
        if (chars[SDLK_DOWN]) {
            dBodyAddForce(ball, 0, -force, 0);
        }

        const dReal* pos = dBodyGetPosition(ball);
        glTranslatef(pos[0], pos[1], pos[2]);
        draw_circle();

        dWorldQuickStep(world, 0.01);
        step();
    }
}
