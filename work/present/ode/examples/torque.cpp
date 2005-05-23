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
        const dReal* pos = dBodyGetPosition(ball);
        const dReal* q = dBodyGetQuaternion(ball);
        double angle = get_q_angle(q);
        const dReal* axis = get_q_axis(q);

        if (chars[SDLK_LEFT]) {
            dBodyAddForceAtPos(ball, -force, 0, 0,
                                     pos[0], pos[1]+1, pos[2]);
        }
        if (chars[SDLK_RIGHT]) {
            dBodyAddForceAtPos(ball, force, 0, 0,
                                     pos[0], pos[1]+1, pos[2]);
        }
        if (chars[SDLK_UP]) {
            dBodyAddForce(ball, 0, +force, 0);
        }
        if (chars[SDLK_DOWN]) {
            dBodyAddForce(ball, 0, -force, 0);
        }

        glTranslatef(pos[0], pos[1], pos[2]);
        glRotatef(angle * 180 / M_PI, axis[0], axis[1], axis[2]);
        draw_circle();

        dWorldQuickStep(world, 0.01);
        step();
    }
}
