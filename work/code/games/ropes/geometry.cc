#include "geometry.h"

dSpaceID COLLIDE_SPACE;
dJointGroupID COLLIDE_JOINTS;

static void near_callback(void* data, dGeomID ga, dGeomID gb) {
    if (dGeomIsSpace(ga) || dGeomIsSpace(gb)) {
        dSpaceCollide2(ga, gb, data, &near_callback);

        if (dGeomIsSpace(ga)) dSpaceCollide(reinterpret_cast<dSpaceID>(ga), data, &near_callback);
        if (dGeomIsSpace(gb)) dSpaceCollide(reinterpret_cast<dSpaceID>(gb), data, &near_callback);
    }
    else {
        dContactGeom geoms[16];
        int n_contacts = dCollide(ga, gb, 16, geoms, sizeof(dContactGeom));
        for (int c = 0; c < n_contacts; c++) {
            dContact contact;
            contact.surface.mode = dContactFDir1 | dContactBounce;
            contact.surface.mu = 0;
            contact.surface.bounce = 0.75;
            contact.surface.bounce_vel = 0.5;
            contact.fdir1[0] = geoms[c].normal[1];
            contact.fdir1[1] = -geoms[c].normal[0];
            contact.fdir1[2] = 0;
            contact.geom = geoms[c];

            dJointID joint = dJointCreateContact(WORLD, COLLIDE_JOINTS, &contact);
            dJointAttach(joint, dGeomGetBody(ga), dGeomGetBody(gb));
        }
    }
}

void collide() {
    dSpaceCollide(COLLIDE_SPACE, 0, &near_callback);
}
