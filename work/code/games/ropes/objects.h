#ifndef __OBJECTS_H__
#define __OBJECTS_H__

#include "common.h"
#include "drawing.h"
#include "geometry.h"
#include <set>

class Object {
    friend class ObjectManager;
public:
    virtual ~Object() { }

    virtual bool visible() const = 0;
    virtual void mark() { }
    virtual void step() { }
    virtual void draw() { }

protected:
    Object() : visible_(false) { }

private:
    Object(const Object&);  // no copying
    
    bool visible_;
    Object* gc_next_;
};

class ObjectManager { 
public:
    ~ObjectManager() {
        for (set_t::iterator i = oset_.begin(); i != oset_.end(); ++i) {
            Object* o = *i;
            delete o;
        }
    }
    
    void add(Object* o) {
        oset_.insert(o);
    }

    void mark(Object* o);

    void sweep();

    void step() {
        for (set_t::iterator i = oset_.begin(); i != oset_.end(); ++i) {
            (*i)->step();
        }
    }
    
    void draw() {
        for (set_t::iterator i = oset_.begin(); i != oset_.end(); ++i) {
            (*i)->draw();
        }
    }

private:
    Object* gc_tail_;
    
    typedef set<Object*> set_t;
    set_t oset_;
};

extern ObjectManager* OBJECT_MANAGER;

class Wall : public Object {
public:
    Wall(vec ll, vec ur) : ll_(ll), ur_(ur), geom_(ll, ur) { }

    bool visible() const { return true; }
    
    void draw() {
        glColor3d(0.7, 0.7, 0.7);
        draw_box(ll_, ur_);
    }
private:
    vec ll_, ur_;
    Box geom_;
};

class Spikey : public Object {
public:
    Spikey(vec p, vec f);

    bool visible() const {
        vec p = body_.position();
        // we don't check off the top of the screen, because stuff falls.
        if (p.x < SCREEN_LEFT || p.x > SCREEN_RIGHT ||
            p.y < SCREEN_BOTTOM) return false;
        else return true;
    }

    void draw() {
        vec p = body_.position();
        glPushMatrix();
            glTranslated(p.x, p.y, 0);
            glColor3d(0,0,1);
            draw_circle(radius);
        glPopMatrix();
    }

    Body* body() { return &body_; }

    static const num radius;
private:
    Circle geom_;
    Body body_;
};

class Rope : public Object {
public:
    Rope(Object* obja, Body* bodya,
         Object* objb, Body* bodyb);

    ~Rope();
    
    void mark() {
        OBJECT_MANAGER->mark(obja_);
        OBJECT_MANAGER->mark(objb_);
    }

    void draw() {
        vec posa = proxya_.position();
        vec posb = proxyb_.position();

        glColor3d(1,1,1);
        glBegin(GL_LINES);
            glVertex2d(posa.x, posa.y);
            glVertex2d(posb.x, posb.y);
        glEnd();
    }

    bool visible() const { return false; }
    
private:
    dJointID rope_;
    dJointID hingea_;
    dJointID hingeb_;
    Body proxya_;
    Body proxyb_;

    Object* obja_;
    Object* objb_;
};

#endif
