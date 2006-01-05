#ifndef __GEOMETRY_H__
#define __GEOMETRY_H__

#include "common.h"
#include "vec.h"
#include "physics.h"

extern dSpaceID COLLIDE_SPACE;
extern dJointGroupID COLLIDE_JOINTS;

class Geom {
public:
    virtual ~Geom() {
        dGeomDestroy(geom_);
    }

    virtual dGeomID geom_id() const { return geom_; }
    virtual dBodyID body_id() const { return dGeomGetBody(geom_); }
    
    virtual Body* body() const { return Body::from_body_id(body_id()); }

    virtual void attach(Body* body) {
        if (body)
            dGeomSetBody(geom_, body->body_id());
        else
            dGeomSetBody(geom_, 0);
    }

    static Geom* from_geom_id(dGeomID geom) {
        if (geom)
            return static_cast<Geom*>(dGeomGetData(geom));
        else
            return 0;
    }

protected:
    virtual void init() {
        dGeomSetData(geom_, static_cast<void*>(this));
    }
    
    dGeomID geom_;
    Geom() : geom_(0) { }

private:
    Geom(const Geom&);  // no copying
};

class Box : public Geom {
public:
    Box(vec ll, vec ur) {
        geom_ = dCreateBox(COLLIDE_SPACE, ur.x - ll.x, ur.y - ll.y, 1);
        init();
        vec center = (ll + ur) / 2;
        dGeomSetPosition(geom_, center.x, center.y, 0);
    }
};

class Circle : public Geom {
public:
    Circle(vec center, num radius) {
        geom_ = dCreateSphere(COLLIDE_SPACE, radius);
        init();
        dGeomSetPosition(geom_, center.x, center.y, 0);
    }
};

void collide();

#endif
