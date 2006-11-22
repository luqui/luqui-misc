#ifndef __UTIL_H__
#define __UTIL_H__

#include <ode/ode.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <GL/glut.h>

struct PhysicsCxt {
	PhysicsCxt() {
		world = dWorldCreate();
		contacts = dJointGroupCreate(0);
		space = dSimpleSpaceCreate(0);
	}

	~PhysicsCxt() {
		dWorldDestroy(world);
	}
	
	dWorldID world;
	dJointGroupID contacts;
	dSpaceID space;
};

void rot_quat(const dQuaternion q)
{
	dReal angle = 2 * acos(q[0]);
	dVector3 axis;
	dReal sina = sqrt(1 - q[0]*q[0]);
	if (fabs(sina) < 0.0005) { sina = 1; }
	axis[0] = q[1] / sina;
	axis[1] = q[2] / sina;
	axis[2] = q[3] / sina;

	glRotatef(180/M_PI * angle, axis[0], axis[1], axis[2]);
}

void draw_circle(double radius) 
{
	glVertex2f(0,0);
	glBegin(GL_TRIANGLE_FAN);
	for (int i = 0; i < 24; i++) {
		double theta = 2*M_PI*i/24;
		glVertex2f(radius*cos(theta), radius*sin(theta));
	}
	glEnd();
}

void draw_text(std::string text) {
	for (int i = 0; i < text.size(); i++) {
		glutBitmapCharacter(GLUT_BITMAP_9_BY_15, text[i]);
	}
}

#endif
