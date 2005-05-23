#include "setup.h"

dWorldID world;

int main(int argc, char** argv)
{
    init_gfx();
    init_2d();
 
    // create world and set gravity   
    world = dWorldCreate();
    dWorldSetGravity(world, 0, -5, 0);
    
    // create a body for our ball
    dBodyID body = dBodyCreate(world);
    dBodySetPosition(body, 0, 0, 0);

    for (;;) {  // infinite loop

        // get the position and move there in OpenGL
        const dReal* pos = dBodyGetPosition(body);
        glTranslatef(pos[0], pos[1], pos[2]);
        
        draw_circle();

        // integrate all bodies
        dWorldQuickStep(world, 0.01);

        // redraw screen
        step();
    }
}
