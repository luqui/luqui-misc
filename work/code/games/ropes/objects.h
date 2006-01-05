#ifndef __OBJECTS_H__
#define __OBJECTS_H__

#include "common.h"
#include "drawing.h"
#include "geometry.h"

class Wall {
public:
    Wall(vec ll, vec ur) : ll_(ll), ur_(ur), geom_(ll, ur) { }

    void draw() {
        glColor3d(0.7, 0.7, 0.7);
        draw_box(ll_, ur_);
    }
private:
    vec ll_, ur_;
    Box geom_;
};

#endif
