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

    void mark(Object* o) {
        if (o->visible_) return;
        o->visible_ = true;
        
        if (gc_tail_) gc_tail_->gc_next_ = o;
        o->gc_next_ = 0;
        gc_tail_ = o;
    }

    void sweep() {
        Object* cptr = 0;
        
        gc_tail_ = 0;
        for (set_t::iterator i = oset_.begin(); i != oset_.end(); ++i) {
            (*i)->visible_ = false;
            if ((*i)->visible()) {
                if (!cptr) cptr = *i;
                mark(*i);
            }
        }

        while (cptr) {
            cptr->mark();
            cptr = cptr->gc_next_;
        }

        int cleaned = 0;
        for (set_t::iterator i = oset_.begin(); i != oset_.end(); ) {
            Object* o = *i;
            if (!o->visible_) {
                set_t::iterator next = i;  ++next;
                oset_.erase(i);
                i = next;

                delete o;
                cleaned++;
            }
            else {
                ++i;
            }
        }

        if (cleaned) cout << "Cleaned up " << cleaned << " objects\n";
    }

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
    Spikey(vec p, vec f) : geom_(p, radius) {
        body_.set_position(p);
        body_.set_owner(static_cast<void*>(this));
        geom_.attach(&body_);
        body_.set_mass(0.1);

        body_.apply_force(f, p);
    }

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

    static const num radius;
private:
    Circle geom_;
    Body body_;
};

const num Spikey::radius = 0.2;

#endif
