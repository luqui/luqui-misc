#include "setup.h"
#include <stdio.h>

dWorldID world;
dJointGroupID contacts;

// from ode.org documentation
void collider(void* data, dGeomID ga, dGeomID gb)
{
    if (dGeomIsSpace(ga) || dGeomIsSpace(gb)) {
        dSpaceCollide2(ga, gb, data, &collider);

        if (dGeomIsSpace(ga)) dSpaceCollide((dSpaceID)ga, data, &collider);
        if (dGeomIsSpace(gb)) dSpaceCollide((dSpaceID)gb, data, &collider);
    }
    else { // we are colliding two objects; generate contact points
        dContactGeom contact_array[16];  
        int num_contacts = dCollide(ga, gb, 16, 
                            contact_array, sizeof(dContactGeom));
        for (int i = 0; i < num_contacts; i++) {
            dContact cgeom;
            cgeom.surface.mode = dContactBounce;
            cgeom.surface.mu = 1.0;
            cgeom.surface.bounce = 0.5;
            cgeom.geom = contact_array[i];
            
            dJointID joint = dJointCreateContact(world, contacts, &cgeom);
            
            dBodyID bodya = dGeomGetBody(ga);
            dBodyID bodyb = dGeomGetBody(gb);
            dJointAttach(joint, bodya, bodyb);
        }
    }
}

int main(int argc, char** argv)
{
    init_gfx();
    init_3d();

    world = dWorldCreate();

    dBodyID bodya = dBodyCreate(world);
    dBodyID bodyb = dBodyCreate(world);

    dBodySetPosition(bodya, -5, 0, 0);
    dBodySetPosition(bodyb, 5, 0.5, 0.2);

    dBodySetLinearVel(bodya, 2, 0, 0);
    dBodySetLinearVel(bodyb, -16, 0, 0);

    dMass massa, massb;
    dMassSetBox(&massa, 1.0, 2, 2, 2);
    dMassSetBox(&massb, 1.0, 1, 1, 1);

    dBodySetMass(bodya, &massa);
    dBodySetMass(bodyb, &massb);

    dSpaceID space = dSimpleSpaceCreate(0);
    dGeomID geoma = dCreateBox(space, 2, 2, 2);
    dGeomSetBody(geoma, bodya);
    dGeomID geomb = dCreateBox(space, 1, 1, 1);
    
    dGeomSetBody(geomb, bodyb);

    contacts = dJointGroupCreate(0);

    for (;;) {
        dJointGroupEmpty(contacts);
        dSpaceCollide(space, NULL, &collider);
        
        glPushMatrix(); {
            const dReal* pos = dBodyGetPosition(bodya);
            const dReal* q   = dBodyGetQuaternion(bodya);
            double angle = get_q_angle(q);
            const dReal* axis = get_q_axis(q);

            glTranslatef(pos[0], pos[1], pos[2]);
            glRotatef(angle * 180 / M_PI, axis[0], axis[1], axis[2]);
            draw_box();
        } glPopMatrix();
        
        glPushMatrix(); {
            const dReal* pos = dBodyGetPosition(bodyb);
            const dReal* q   = dBodyGetQuaternion(bodyb);
            double angle = get_q_angle(q);
            const dReal* axis = get_q_axis(q);

            glTranslatef(pos[0], pos[1], pos[2]);
            glRotatef(angle * 180 / M_PI, axis[0], axis[1], axis[2]);
            glScalef(0.5, 0.5, 0.5);
            draw_box();
        } glPopMatrix();

        dWorldQuickStep(world, 0.01);
        
        step();
    }
}
