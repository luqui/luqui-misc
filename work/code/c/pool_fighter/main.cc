#include <cstdlib>
#include <soy/init.h>
#include <soy/Timer.h>
#include <soy/Viewport.h>
#include <soy/vec2.h>
#include <soy/util.h>
#include <ode/ode.h>
#include <GL/glut.h>
#include <string>
#include <sstream>
#include <list>
#include <set>
#include <iomanip>

#include "Ball.h"

const double DT = 1/60.0;

dWorldID WORLD;
dSpaceID SPACE;
dJointGroupID CONTACTS;

int LIVES;
double TIME;

void draw_circle(double radius = 1);
void rot_quat(const dQuaternion q);
void spawn_enemy(vec2 pos = vec2());

struct Hole {
	Hole(vec2 pos, double radius) : pos(pos), radius(radius) { }

	vec2 pos;
	double radius;

	void draw() {
		glPushMatrix();
		glTranslatef(pos.x, pos.y, 0);
		glColor3f(0,0.3,0.7);
		draw_circle(radius);
		glPopMatrix();
	}
};

struct Player {
	vec2 pos;
	ShotFactory* factory;
};

SoyInit INIT;
Viewport VIEW(vec2(0,16), vec2(48,36));

Player PLAYER;

vec2 MOUSE;

typedef std::list<Ball*> balls_t;
balls_t BALLS;

std::set<Ball*> DELETE_SET;

typedef std::list<Hole*> holes_t;
holes_t HOLES;

void set_wall(dGeomID geom) {
	dGeomSetCategoryBits(geom, CAT_WALL);
	dGeomSetCollideBits(geom, CAT_ENEMY);
}

void init()
{
	srand(time(NULL));
	
	INIT.set_fullscreen();
	INIT.init();
	SDL_ShowCursor(0);
	VIEW.activate();

	WORLD = dWorldCreate();
	SPACE = dSimpleSpaceCreate(0);
	CONTACTS = dJointGroupCreate(0);

	set_wall(dCreatePlane(SPACE, -1,  0, 0, -24));
	set_wall(dCreatePlane(SPACE,  1,  0, 0, -24));
	set_wall(dCreatePlane(SPACE,  0, -1, 0, -34));

	HOLES.push_back(new Hole(vec2(-21, 31),  3));
	HOLES.push_back(new Hole(vec2( 21, 31),  3));

	PLAYER.factory = new NormalShotFactory;
}

void check_collision(void* data, dGeomID ga, dGeomID gb) 
{
	if (dGeomIsSpace(ga) || dGeomIsSpace(gb)) {
		// collide a space with the other object
		dSpaceCollide2(ga, gb, data, &check_collision);
		// check for collisions internally to the space
		if (dGeomIsSpace(ga)) dSpaceCollide(dSpaceID(ga), data, &check_collision);
		if (dGeomIsSpace(gb)) dSpaceCollide(dSpaceID(gb), data, &check_collision);
	}
	else {
		const int max_contacts = 16;
		dContactGeom contacts[max_contacts];
		int ncontacts = dCollide(ga, gb, max_contacts, contacts, sizeof(dContactGeom));

		if (ncontacts > 0) {
			Ball* ba = (Ball*)dGeomGetData(ga);
			Ball* bb = (Ball*)dGeomGetData(gb);
			if (ba && bb && dynamic_cast<Shot*>(ba) && dynamic_cast<Shot*>(bb)) {
				DELETE_SET.insert(ba);
				DELETE_SET.insert(bb);
				spawn_enemy(ba->pos());
			}
		}

		for (int i = 0; i < ncontacts; i++) {
			dContact contact;
			contact.geom = contacts[i];
			contact.surface.mode = dContactBounce;
			contact.surface.mu = dInfinity;
			contact.surface.bounce = 1;
			contact.surface.bounce_vel = 1;

			dJointID ctct = dJointCreateContact(WORLD, CONTACTS, &contact);
			dJointAttach(ctct, dGeomGetBody(ga), dGeomGetBody(gb));
		}
	}
}

double HIT = 0;

void draw_status_bar()
{
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glColor4f(0.5, 0.5, 0.5, 0.25);
	glBegin(GL_QUADS);
		glVertex2f(-24, 34);
		glVertex2f( 24, 34);
		glVertex2f( 24, 32);
		glVertex2f(-24, 32);
	glEnd();
	glDisable(GL_BLEND);

	glColor3f(0.7, 0.7, 0.7);
	for (int i = 0; i < LIVES; i++) {
		double left = -2 + 2*i;
		double width = 1;
		glBegin(GL_QUADS);
			glVertex2f(left, 33.5);
			glVertex2f(left + width, 33.5);
			glVertex2f(left + width, 32.5);
			glVertex2f(left, 32.5);
		glEnd();
	}

	glPushMatrix();
	glTranslatef(10, 33, 0);
	glScalef(0.75, 0.75, 1);
	PLAYER.factory->draw_icon();
	glPopMatrix();

	std::stringstream ss;
	ss << int(TIME/60) << ":";
	ss.width(2);
	ss.fill('0');
	ss << int(TIME)%60;
	glColor3f(1,1,1);
	glRasterPos2f(-10, 32.5);
	draw_text(ss.str());
}

void draw()
{
	glPushMatrix();
	glTranslatef(PLAYER.pos.x, PLAYER.pos.y, 0);
	glColor3f(0.7, 0.7, 0.7);
	glBegin(GL_QUADS);
		glVertex2f(-0.5, -0.5);
		glVertex2f( 0.5, -0.5);
		glVertex2f( 0.5,  0.5);
		glVertex2f(-0.5,  0.5);
	glEnd();

	vec2 pointing = (MOUSE - PLAYER.pos);
	glLineWidth(1.0);
	glColor3f(0,0,1);
	glBegin(GL_LINES);
		glVertex2f(0,0);
		glVertex2f(pointing.x, pointing.y);
	glEnd();
	glPopMatrix();

	for (balls_t::iterator i = BALLS.begin(); i != BALLS.end(); ++i) {
		(*i)->draw();
	}
	for (holes_t::iterator i = HOLES.begin(); i != HOLES.end(); ++i) {
		(*i)->draw();
	}
	
	draw_status_bar();

	if (HIT > 0) {
		glEnable(GL_BLEND);
		glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
		glColor4f(1, 0, 0, HIT);
		glBegin(GL_QUADS);
			glVertex2f(VIEW.center.x - VIEW.dim.x, VIEW.center.y - VIEW.dim.y);
			glVertex2f(VIEW.center.x + VIEW.dim.x, VIEW.center.y - VIEW.dim.y);
			glVertex2f(VIEW.center.x + VIEW.dim.x, VIEW.center.y + VIEW.dim.y);
			glVertex2f(VIEW.center.x - VIEW.dim.x, VIEW.center.y + VIEW.dim.y);
		glEnd();
		glDisable(GL_BLEND);
	}
}

int shots_till_enemy = 3;

void spawn_enemy(vec2 pos) {
	if (pos.norm2() == 0) {
		for (int tries = 0; tries < 10; tries++) {
			pos = vec2(randrange(-20, 20), randrange(10, 30));
			bool again = false;
			for (balls_t::iterator i = BALLS.begin(); i != BALLS.end(); ++i) {
				if ((pos - (*i)->pos()).norm() < 1.2 + (*i)->radius()) {
					again = true;
					break;
				}
			}

			if (!again) break;
		}
	}
	
	Enemy* enemy = new Enemy;
	dBodySetPosition(enemy->body, pos.x, pos.y, 0);
	BALLS.push_back(enemy);
}

void step()
{
	HIT -= 5*DT;
	if (HIT < 0) HIT = 0;

	TIME += DT;
	
	while (shots_till_enemy <= 0) {
		spawn_enemy();
		shots_till_enemy += 3;
	}
	
	for (balls_t::iterator i = BALLS.begin(); i != BALLS.end(); ) {
		vec2 pos = (*i)->pos();
		dReal radius = (*i)->radius();
		(*i)->step();
		
		bool kill = false;
		for (holes_t::iterator j = HOLES.begin(); j != HOLES.end(); ++j) {
			if ((pos - (*j)->pos).norm() + radius < (*j)->radius) {
				// ball fell in hole
				kill = true;
				break;
			}
		}

		if (pos.x + radius < VIEW.center.x - VIEW.dim.x/2
		 || pos.x - radius > VIEW.center.x + VIEW.dim.x/2
		 || pos.y + radius < VIEW.center.y - VIEW.dim.y/2
		 || pos.y - radius > VIEW.center.y + VIEW.dim.y/2) {
			kill = true;
			if (dynamic_cast<Enemy*>(*i)) {
				LIVES--;
				HIT = 1;
				spawn_enemy();
			}
		}

		std::set<Ball*>::iterator del = DELETE_SET.find(*i);
		if (del != DELETE_SET.end()) {
			kill = true;
			DELETE_SET.erase(del);
		}

		if (kill) {
			balls_t::iterator k = i;
			++i;
			delete *k;
			BALLS.erase(k);
		}
		else {
			++i;
		}
	}

	dSpaceCollide(SPACE, 0, &check_collision);
	dWorldQuickStep(WORLD, DT);
	dJointGroupEmpty(CONTACTS);
}

bool SHOOTING = false;

void events()
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
			SDL_Quit();
			exit(0);
		}

		if (e.type == SDL_MOUSEBUTTONDOWN && e.button.button == SDL_BUTTON_LEFT) {
			SHOOTING = true;
		}
		if (e.type == SDL_MOUSEBUTTONUP && e.button.button == SDL_BUTTON_LEFT) {
			Shot* ball = PLAYER.factory->fire(PLAYER.pos, MOUSE - PLAYER.pos);
			BALLS.push_back(ball);
			shots_till_enemy--;
			SHOOTING = false;

			vec2 mousepos = coord_convert(VIEW, INIT.pixel_view(), PLAYER.pos);
			SDL_WarpMouse(int(mousepos.x), int(mousepos.y));
		}
	}

	int mx, my;
	SDL_GetMouseState(&mx, &my);
	MOUSE = coord_convert(INIT.pixel_view(), VIEW, vec2(mx, my));

	if (!SHOOTING) {
		PLAYER.pos = MOUSE;
	}
}

void death_screen()
{
	glClear(GL_COLOR_BUFFER_BIT);
	glColor3f(0.4,0,0);
	glBegin(GL_QUADS);
		glVertex2f(VIEW.center.x - VIEW.dim.x, VIEW.center.y - VIEW.dim.y);
		glVertex2f(VIEW.center.x + VIEW.dim.x, VIEW.center.y - VIEW.dim.y);
		glVertex2f(VIEW.center.x + VIEW.dim.x, VIEW.center.y + VIEW.dim.y);
		glVertex2f(VIEW.center.x - VIEW.dim.x, VIEW.center.y + VIEW.dim.y);
	glEnd();

	glColor3f(1,1,1);
	glRasterPos2f(-1, 16);
	draw_text("Game Over");
	draw_status_bar();
	SDL_GL_SwapBuffers();

	SDL_Event e;
	while (SDL_WaitEvent(&e)) {
		if (e.type == SDL_KEYDOWN || e.type == SDL_MOUSEBUTTONDOWN) {
			return;
		}
	}
}

void reset() {
	for (balls_t::iterator i = BALLS.begin(); i != BALLS.end(); ++i) {
		delete *i;
	}
	BALLS.clear();

	for (int i = 0; i < 7; i++) {
		spawn_enemy();
	}

	TIME = 0;
	LIVES = 2;
}

int main()
{
	FrameRateLockTimer timer(DT);
	init();
	reset();
	
	while (true) {
		events();
		step();

		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
		
		timer.lock();

		if (LIVES < 0) { death_screen(); reset(); }
	}
}
