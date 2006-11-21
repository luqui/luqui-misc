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

enum {
	CAT_CUEBALL = 0x1,
	CAT_WALL    = 0x2,
	CAT_ENEMY   = 0x4
};

const double DT = 1/60.0;

dWorldID WORLD;
dSpaceID SPACE;
dJointGroupID CONTACTS;

int SCORE = 0;

void draw_circle(double radius = 1);
void rot_quat(const dQuaternion q);

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

class Ball {
public:
	Ball(double radius) : body(dBodyCreate(WORLD)), geom(dCreateSphere(SPACE, radius)),
						  plane2d(dJointCreatePlane2D(WORLD, 0)) {
		dJointAttach(plane2d, body, 0);
		dGeomSetBody(geom, body);
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

	virtual void draw_self() const {
		dReal rad = radius();
		glColor3f(1,1,1);
		draw_circle(rad);
		glColor3f(0,0,0);
		glBegin(GL_LINES);
			glVertex2f(0,0);
			glVertex2f(rad,0);
		glEnd();
	}
	
	virtual void step() { }

	virtual int price() const { return 0; }

	dBodyID body;
	dGeomID geom;
	dJointID plane2d;
};

class Enemy : public Ball {
public:
	Enemy() : Ball(1), fade_in(0) {
		dGeomSetCategoryBits(geom, CAT_ENEMY);
		dGeomSetCollideBits(geom, CAT_CUEBALL | CAT_ENEMY | CAT_WALL);
	}

	void draw_self() const {
		dReal rad = radius();
		glEnable(GL_BLEND);
		glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
		glColor4f(1,0,0, fade_in);
		draw_circle(rad);
		glDisable(GL_BLEND);
	}

	void step() {
		fade_in += DT;
		if (fade_in > 1) fade_in = 1;
	}

	int price() const { return 10; }

private:
	double fade_in;
};



struct Player {
	vec2 pos;
};

SoyInit INIT;
Viewport VIEW(vec2(0,16), vec2(48,36));

Player PLAYER;

vec2 MOUSE;

typedef std::list<Ball*> balls_t;
balls_t BALLS;

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
	VIEW.activate();

	WORLD = dWorldCreate();
	SPACE = dSimpleSpaceCreate(0);
	CONTACTS = dJointGroupCreate(0);

	set_wall(dCreatePlane(SPACE, -1,  0, 0, -24));
	set_wall(dCreatePlane(SPACE,  1,  0, 0, -24));
	set_wall(dCreatePlane(SPACE,  0, -1, 0, -34));
	set_wall(dCreatePlane(SPACE,  0,  1, 0, -2));

	HOLES.push_back(new Hole(vec2(-21, 15),  3));
	HOLES.push_back(new Hole(vec2(-21, 31),  3));
	HOLES.push_back(new Hole(vec2( 21, 15),  3));
	HOLES.push_back(new Hole(vec2( 21, 31),  3));
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

		for (int i = 0; i < ncontacts; i++) {
			dContact contact;
			contact.geom = contacts[i];
			contact.surface.mode = dContactBounce;
			contact.surface.mu = 10;
			contact.surface.bounce = 0.8;
			contact.surface.bounce_vel = 1;

			dJointID ctct = dJointCreateContact(WORLD, CONTACTS, &contact);
			dJointAttach(ctct, dGeomGetBody(ga), dGeomGetBody(gb));
		}
	}
}

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

	vec2 pointing = ~(MOUSE - PLAYER.pos);
	glLineWidth(2.0);
	glColor3f(1,0,0);
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

	std::stringstream ss;
	ss << SCORE;
	glColor3f(1,1,1);
	glRasterPos2f(-2, 32);
	draw_text(ss.str());
}

double enemy_timer = 1;

void step()
{
	enemy_timer -= DT;
	while (enemy_timer < 0) {
		Enemy* enemy = new Enemy;
		dBodySetPosition(enemy->body, randrange(-20, 20), randrange(15, 32), 0);
		dBodySetLinearVel(enemy->body, 0, -0.5, 0);
		BALLS.push_back(enemy);
		enemy_timer += 10;
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

		if (pos.x < VIEW.center.x - VIEW.dim.x/2
		 || pos.x > VIEW.center.x + VIEW.dim.x/2
		 || pos.y < VIEW.center.y - VIEW.dim.y/2
		 || pos.y > VIEW.center.y + VIEW.dim.y/2) {
			kill = true;
		}

		if (kill) {
			SCORE += (*i)->price();
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

void events()
{
	vec2 vel;
	Uint8* keys = SDL_GetKeyState(NULL);
	if (keys[SDLK_a]) { vel.x -= 5; }
	if (keys[SDLK_d]) { vel.x += 5; }
	
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
			SDL_Quit();
			exit(0);
		}

		if (e.type == SDL_MOUSEBUTTONDOWN && e.button.button == SDL_BUTTON_LEFT) {
			Ball* ball = new Ball(1);
			dBodySetPosition(ball->body, PLAYER.pos.x, PLAYER.pos.y, 0);
			vec2 pointing = 5*~(MOUSE - PLAYER.pos);
			dBodySetLinearVel(ball->body, pointing.x, pointing.y, 0);
			dGeomSetCategoryBits(ball->geom, CAT_CUEBALL);
			dGeomSetCollideBits(ball->geom, CAT_CUEBALL | CAT_ENEMY);
			BALLS.push_back(ball);
		}
	}

	int mx, my;
	SDL_GetMouseState(&mx, &my);
	MOUSE = coord_convert(INIT.pixel_view(), VIEW, vec2(mx, my));

	PLAYER.pos += DT * vel;
}

int main()
{
	FrameRateLockTimer timer(DT);
	init();
	
	while (true) {
		events();
		step();

		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
		
		timer.lock();
	}
}
