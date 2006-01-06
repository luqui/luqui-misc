#ifndef __DRAWING_H__
#define __DRAWING_H__

#include "common.h"
#include "vec.h"

struct Color {
    Color() : r(0), g(0), b(0) { }
    Color(num r, num g, num b) : r(r), g(g), b(b) { }
    num r, g, b;
};

void draw_circle();

void draw_circle(num radius);

void draw_box(vec ll, vec ur);

#endif
