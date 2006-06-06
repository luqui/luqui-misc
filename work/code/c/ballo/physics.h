#ifndef __PHYSICS_H__
#define __PHYSICS_H__

#include "config.h"
#include "vec.h"
#include <ode/ode.h>

extern dWorldID WORLD;
extern num OVERSTEP;
extern const num STEP;

void init_ode();

class Body
{
public:
	Body() 
		: body_(dBodyCreate(WORLD)),
		  plane2d_(dJointCreatePlane2D(WORLD, 0))
	{
		dJointAttach(plane2d_, body_, 0);
	}

	~Body() {
		dJointDestroy(plane2d_);
		dBodyDestroy(body_);
	}

	void set_pos(vec posin) {
		dBodySetPosition(body_, posin.x, posin.y, 0);
	}

	vec pos() const { 
		const dReal* posout = dBodyGetPosition(body_);
		return vec(posout[0], posout[1]);
	}

	void set_vel(vec velin) {
		dBodySetLinearVel(body_, velin.x, velin.y, 0);
	}

	vec vel() const {
		const dReal* velout = dBodyGetLinearVel(body_);
		return vec(velout[0], velout[1]);
	}

	vec drawing_pos() const {
		return pos() + OVERSTEP * vel();
	}
	
protected:
	dBodyID body_;
	dJointID plane2d_;
};

#endif
