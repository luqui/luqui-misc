#ifndef __PLAYER_H__
#define __PLAYER_H__

#include "common.h"
#include "vec.h"
#include "drawing.h"
#include "physics.h"
#include "geometry.h"
#include "input.h"
#include "objects.h"
#include <list>

class Player : public MouseSelector, public Object {
public:
    Player(vec pos) : spikey_(0), angle_(0), geom_(pos, radius) {
        body_.set_position(pos);
        body_.set_owner(static_cast<void*>(this));
        geom_.attach(&body_);
    }

    static const num radius;
    
    void step() { }
    void draw() {
        vec pos = body_.position();
        glPushMatrix();
            glTranslated(pos.x, pos.y, 0);
            glRotated(angle_ * 180 / M_PI, 0, 0, 1);
            
            glColor3d(0,0,1);
            draw_circle(radius); 
            
            glColor3d(1,1,1);
            glTranslated(2*radius, 0, 0);
            draw_circle(0.1);
            glTranslated(2*radius, 0, 0);
            draw_circle(0.2);
        glPopMatrix();
    }

    void mouse_move(vec dir) {
        num amt = dir * vec(1,0) * -0.4;   // only horizontal motion
        angle_ += amt;
        angle_ = smallmod(angle_, 2*M_PI);
    }

    void mouse_left_button_down() {
        num dist = radius + Spikey::radius;
        vec dir = vec(cos(angle_), sin(angle_));
        vec pos = body_.position();
        spikey_ = new Spikey(pos + dist*dir, dir / STEP);
        body_.apply_force(-dir / STEP, pos);  // newton's 3rd
        OBJECT_MANAGER->add(spikey_);
    }

    void mouse_left_button_up() {
        if (!spikey_) return;
        Rope* rope = new Rope(this, &body_, spikey_, spikey_->body());
        ropes_.push_back(rope);
        OBJECT_MANAGER->add(rope);
    }

    void mark() {
        if (spikey_) OBJECT_MANAGER->mark(spikey_);
        for (ropes_t::iterator i = ropes_.begin(); i != ropes_.end(); ++i) {
            OBJECT_MANAGER->mark(*i);
        }
    }

    bool visible() const { return true; }

private:
    Player(const Player&);  // no copying of players

    Spikey* spikey_;

    num angle_;
    Body body_;
    Circle geom_;

    typedef list<Rope*> ropes_t;
    ropes_t ropes_;
};

const num Player::radius = 1;

#endif
