#ifndef __DRAWING_H__
#define __DRAWING_H__

#include "common.h"
#include "vec.h"

void draw_circle() {
    static int dlist = 0;
    if (dlist) {
        glCallList(dlist);
    }
    else {
        dlist = glGenLists(1);
        glNewList(dlist, GL_COMPILE_AND_EXECUTE);
            num theta = 0;
            glBegin(GL_TRIANGLE_FAN);
                glVertex2d(0,0);
                for (int i = 0; i <= 24; i++, theta += M_PI/12) {
                    glVertex2d(cos(theta), sin(theta));
                }
            glEnd();
        glEndList();
    }
}

void draw_circle(num radius) {
    glPushMatrix();
    glScaled(radius, radius, 0);
    draw_circle();
    glPopMatrix();
}

void draw_box(vec ll, vec ur) {
    glBegin(GL_QUADS);
        glVertex2d(ll.x, ll.y);
        glVertex2d(ur.x, ll.y);
        glVertex2d(ur.x, ur.y);
        glVertex2d(ll.x, ur.y);
    glEnd();
}

#endif
