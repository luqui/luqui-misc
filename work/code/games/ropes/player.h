#ifndef __PLAYER_H__
#define __PLAYER_H__

#include "common.h"
#include "vec.h"
#include "drawing.h"
#include "physics.h"
#include "geometry.h"
#include "input.h"

class Player : public MouseSelector {
public:
    Player(vec pos) : motion(0), geom_(pos, 1) {
        body_.set_position(pos);
        geom_.attach(&body_);
    }
    
    void step() { 
        body_.set_angular_velocity(motion / STEP);
        motion = 0;
    }
    void draw() {
        vec pos = body_.position();
        num angle = body_.angle();
        glPushMatrix();
            glTranslated(pos.x, pos.y, 0);
            glRotated(angle * 180 / M_PI, 0, 0, 1);
            
            glColor3d(0,0,1);
            draw_circle(); 
            
            glColor3d(1,1,1);
            glBegin(GL_LINES);
                glVertex2d(0, 0);
                glVertex2d(1, 0);
            glEnd();
        glPopMatrix();
    }

    void mouse_move(vec dir) {
        num amt = dir * vec(1,0) * 0.1;   // only horizontal motion
        motion += amt;
    }

private:
    Player(const Player&);  // no copying of players

    num motion;
    Body body_;
    Circle geom_;
};

#endif
