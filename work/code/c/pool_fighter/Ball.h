#ifndef __BALL_H__
#define __BALL_H__

#include "util.h"
#include <ode/ode.h>

enum {
	CAT_CUEBALL = 0x1,
	CAT_WALL    = 0x2,
	CAT_ENEMY   = 0x4
};

extern dWorldID WORLD;
extern dSpaceID SPACE;
extern const double DT;

class Ball {
public:
	Ball(double radius) : body(dBodyCreate(WORLD)), geom(dCreateSphere(SPACE, radius)),
						  plane2d(dJointCreatePlane2D(WORLD, 0)) {
		dJointAttach(plane2d, body, 0);
		dGeomSetBody(geom, body);
		dGeomSetData(geom, this);
	}
	virtual ~Ball() {
		dJointDestroy(plane2d);
		dBodyDestroy(body);
		dGeomDestroy(geom);
	}

	vec2 pos() const {
		const dReal* ppos = dBodyGetPosition(body);
		return vec2(ppos[0], ppos[1]);
	}

	vec2 vel() const {
		const dReal* pvel = dBodyGetLinearVel(body);
		return vec2(pvel[0], pvel[1]);
	}

	dReal radius() const {
		return dGeomSphereGetRadius(geom);
	}

	virtual void draw() const {
		vec2 posi = pos();

		glPushMatrix();
		glTranslatef(posi.x, posi.y, 0);
		
		rot_quat(dBodyGetQuaternion(body));
		draw_self();
		glPopMatrix();
	}

	virtual void draw_self() const = 0;
	
	virtual void step() { }

	virtual int price() const { return 0; }

	dBodyID body;
	dGeomID geom;
	dJointID plane2d;
};

const double shot_radius = 0.8;
const double shot_mass = 1.2;

class Shot : public Ball {
public:
	Shot() : Ball(shot_radius) { 
		dMass mass;
		dMassSetSphere(&mass, shot_mass / (4/3 * M_PI * shot_radius*shot_radius*shot_radius), shot_radius);
		dBodySetMass(body, &mass);
		dGeomSetCategoryBits(geom, CAT_CUEBALL);
		dGeomSetCollideBits(geom, CAT_CUEBALL | CAT_ENEMY);
	}

	void draw_self() const {
		dReal rad = radius();
		glColor3f(1,1,1);
		draw_circle(rad);
		glColor3f(0,0,0);
		glBegin(GL_LINES);
			glVertex2f(0,0);
			glVertex2f(rad,0);
		glEnd();
	}
};

class ShotFactory
{
public:
	virtual ~ShotFactory() { }

	virtual Shot* fire(vec2 pos, vec2 dir) = 0;
	virtual void draw_icon() const = 0;
};

class NormalShotFactory : public ShotFactory
{
public:
	Shot* fire(vec2 pos, vec2 dir) {
		Shot* ball = new Shot;
		dBodySetPosition(ball->body, pos.x, pos.y, 0);
		dBodySetLinearVel(ball->body, dir.x, dir.y, 0);
		return ball;
	}

	void draw_icon() const {
		glColor3f(1,1,1);
		draw_circle(0.8);
		glColor3f(0,0,0);
		glBegin(GL_LINES);
			glVertex2f(0,0);
			glVertex2f(0.8,0);
		glEnd();
	}
};


class Enemy : public Ball {
public:
	Enemy() : Ball(1.2), fade_in(0) {
		dGeomSetCategoryBits(geom, CAT_ENEMY);
		dGeomSetCollideBits(geom, CAT_CUEBALL | CAT_ENEMY | CAT_WALL);
	}

	void draw_self() const {
		dReal rad = radius();
		glEnable(GL_BLEND);
		glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
		glColor4f(1,0,0, fade_in);
		draw_circle(rad);
		glColor4f(0,0,0, fade_in);
		glBegin(GL_LINES);
			glVertex2f(0,0);
			glVertex2f(rad,0);
		glEnd();
		glDisable(GL_BLEND);
	}

	void step() {
		fade_in += DT;
		if (fade_in > 1) fade_in = 1;

		vec2 damp = -0.1 * (vel() - vec2(0, -0.7));
		dBodyAddForce(body, damp.x, damp.y, 0);
	}

	int price() const { return 1; }

private:
	double fade_in;
};

#endif
