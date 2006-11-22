#ifndef __GAMEMODE_H__
#define __GAMEMODE_H__

#include <soy/vec2.h>
#include <soy/vec3.h>
#include <soy/Viewport.h>

class GameMode;

extern vec2 MOUSE;
extern Viewport VIEW;
extern SoyInit INIT;
extern GameMode* MODE;

class GameMode
{
public:
	virtual ~GameMode() { }

	virtual void draw() const = 0;
	virtual void step() = 0;
	virtual bool events(const SDL_Event& e) = 0;
};

struct Pocket {
	Pocket(vec2 pos, double radius) : pos(pos), radius(radius) { }

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
	Player() : factory(0) { }
	~Player() {
		delete factory;
	}
	
	vec2 pos;
	ShotFactory* factory;
};


void collision_callback(void* data, dGeomID ga, dGeomID gb);

class GameOverMode : public GameMode
{
public:
	GameOverMode(vec3 color, double time, int lives) 
		: color_(color), time_(time), lives_(lives) 
	{ }

	void draw() const {
		// cut-paste evilness
		glColor3f(color_.x, color_.y, color_.z);
		glBegin(GL_QUADS);
			glVertex2f(VIEW.center.x - VIEW.dim.x, VIEW.center.y - VIEW.dim.y);
			glVertex2f(VIEW.center.x + VIEW.dim.x, VIEW.center.y - VIEW.dim.y);
			glVertex2f(VIEW.center.x + VIEW.dim.x, VIEW.center.y + VIEW.dim.y);
			glVertex2f(VIEW.center.x - VIEW.dim.x, VIEW.center.y + VIEW.dim.y);
		glEnd();
		
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
		for (int i = 0; i < lives_; i++) {
			double left = -2 + 2*i;
			double width = 1;
			glBegin(GL_QUADS);
				glVertex2f(left, 33.5);
				glVertex2f(left + width, 33.5);
				glVertex2f(left + width, 32.5);
				glVertex2f(left, 32.5);
			glEnd();
		}

		std::stringstream ss;
		ss << int(time_/60) << ":";
		ss.width(2);
		ss.fill('0');
		ss << int(time_)%60;
		glColor3f(1,1,1);
		glRasterPos2f(-10, 32.5);
		draw_text(ss.str());
	}

	void step() { }

	bool events(const SDL_Event& e);
private:
	vec3 color_;
	double time_;
	int lives_;
};

class PoolMode : public GameMode
{
public:
	PoolMode() 
	  : shooting_(false),
		phys_(new PhysicsCxt) 
	{
		holes_.push_back(new Pocket(vec2(-21,31), 3));
		holes_.push_back(new Pocket(vec2(21,31), 3));
	}

	~PoolMode() {
		for (balls_t::iterator i = balls_.begin(); i != balls_.end(); ++i) {
			delete *i;
		}
		for (holes_t::iterator i = holes_.begin(); i != holes_.end(); ++i) {
			delete *i;
		}
		delete phys_;
	}
	
	virtual void check_collision(dGeomID ga, dGeomID gb) {
		if (dGeomIsSpace(ga) || dGeomIsSpace(gb)) {
			// collide a space with the other object
			dSpaceCollide2(ga, gb, this, &collision_callback);
			// check for collisions internally to the space
			if (dGeomIsSpace(ga)) dSpaceCollide(dSpaceID(ga), this, &collision_callback);
			if (dGeomIsSpace(gb)) dSpaceCollide(dSpaceID(gb), this, &collision_callback);
		}
		else {
			const int max_contacts = 16;
			dContactGeom contacts[max_contacts];
			int ncontacts = dCollide(ga, gb, max_contacts, contacts, sizeof(dContactGeom));

			if (ncontacts > 0) {
				Ball* ba = (Ball*)dGeomGetData(ga);
				Ball* bb = (Ball*)dGeomGetData(gb);
				if (ba && bb && dynamic_cast<Shot*>(ba) && dynamic_cast<Shot*>(bb)) {
					delete_set_.insert(ba);
					delete_set_.insert(bb);
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

				dJointID ctct = dJointCreateContact(phys_->world, phys_->contacts, &contact);
				dJointAttach(ctct, dGeomGetBody(ga), dGeomGetBody(gb));
			}
		}
	}

	void draw() const {
		glPushMatrix();
		glTranslatef(player_.pos.x, player_.pos.y, 0);
		glColor3f(0.7, 0.7, 0.7);
		glBegin(GL_QUADS);
			glVertex2f(-0.5, -0.5);
			glVertex2f( 0.5, -0.5);
			glVertex2f( 0.5,  0.5);
			glVertex2f(-0.5,  0.5);
		glEnd();

		vec2 pointing = (MOUSE - player_.pos);
		glLineWidth(1.0);
		glColor3f(0,0,1);
		glBegin(GL_LINES);
			glVertex2f(0,0);
			glVertex2f(pointing.x, pointing.y);
		glEnd();
		glPopMatrix();

		for (balls_t::const_iterator i = balls_.begin(); i != balls_.end(); ++i) {
			(*i)->draw();
		}
		for (holes_t::const_iterator i = holes_.begin(); i != holes_.end(); ++i) {
			(*i)->draw();
		}
		
		draw_status_bar();
	}

	void step() {
		for (balls_t::iterator i = balls_.begin(); i != balls_.end(); ) {
			vec2 pos = (*i)->pos();
			dReal radius = (*i)->radius();
			(*i)->step();
			
			bool kill = false;
			for (holes_t::iterator j = holes_.begin(); j != holes_.end(); ++j) {
				if ((pos - (*j)->pos).norm() + radius < (*j)->radius) {
					// ball fell in hole
					ball_in_hole(*i, *j);

					kill = true;
					break;
				}
			}

			if (pos.x + radius < VIEW.center.x - VIEW.dim.x/2
			 || pos.x - radius > VIEW.center.x + VIEW.dim.x/2
			 || pos.y + radius < VIEW.center.y - VIEW.dim.y/2
			 || pos.y - radius > VIEW.center.y + VIEW.dim.y/2) {
				ball_off_screen(*i);
				
				kill = true;
			}

			std::set<Ball*>::iterator del = delete_set_.find(*i);
			if (del != delete_set_.end()) {
				kill = true;
				delete_set_.erase(del);
			}

			if (kill) {
				balls_t::iterator k = i;
				++i;
				delete *k;
				balls_.erase(k);
			}
			else {
				++i;
			}
		}

		dSpaceCollide(phys_->space, this, &collision_callback);
		dWorldQuickStep(phys_->world, DT);
		dJointGroupEmpty(phys_->contacts);
	
		if (!shooting_) {
			player_.pos = MOUSE;
		}
	}

	bool events(const SDL_Event& e) {
		if (e.type == SDL_MOUSEBUTTONDOWN && e.button.button == SDL_BUTTON_LEFT) {
			shooting_ = true;
			return true;
		}
		if (e.type == SDL_MOUSEBUTTONUP && e.button.button == SDL_BUTTON_LEFT) {
			if (shooting_) {
				shoot();
				shooting_ = false;

				vec2 mousepos = coord_convert(VIEW, INIT.pixel_view(), player_.pos);
				SDL_WarpMouse(int(mousepos.x), int(mousepos.y));
			}
			return true;
		}
		return false;
	}

protected:
	PhysicsCxt* phys_;
	Player player_;

	typedef std::list<Ball*> balls_t;
	balls_t balls_;
	typedef std::set<Ball*> delete_set_t;
	delete_set_t delete_set_;
	typedef std::list<Pocket*> holes_t;
	holes_t holes_;

	bool shooting_;
	
	virtual void ball_off_screen(Ball* ball) { }

	virtual void ball_in_hole(Ball* ball, Pocket* hole) { }

	virtual void shoot() {
		Shot* ball = player_.factory->fire(player_.pos, MOUSE - player_.pos);
		balls_.push_back(ball);
	}

	virtual void make_wall(vec2 facing, vec2 ref) {
		dGeomID wall = dCreatePlane(phys_->space, facing.x, facing.y, 0, facing * ref);
		dGeomSetCategoryBits(wall, CAT_WALL);
		dGeomSetCollideBits(wall, CAT_ENEMY);
	}

	virtual void draw_status_bar() const {
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

		if (player_.factory) {
			glPushMatrix();
			glTranslatef(10, 33, 0);
			glScalef(0.75, 0.75, 1);
			player_.factory->draw_icon();
			glPopMatrix();
		}
	}

	virtual void spawn_enemy(vec2 pos = vec2()) {
		if (pos.norm2() == 0) {
			for (int tries = 0; tries < 10; tries++) {
				pos = vec2(randrange(-20, 20), randrange(10, 30));
				bool again = false;
				for (balls_t::iterator i = balls_.begin(); i != balls_.end(); ++i) {
					if ((pos - (*i)->pos()).norm() < 1.2 + (*i)->radius()) {
						again = true;
						break;
					}
				}

				if (!again) break;
			}
		}
		
		Enemy* enemy = new Enemy(phys_);
		dBodySetPosition(enemy->body, pos.x, pos.y, 0);
		balls_.push_back(enemy);
	}
};

void collision_callback(void* data, dGeomID ga, dGeomID gb) {
	((PoolMode*)data)->check_collision(ga, gb);
}

class GravityMode : public PoolMode
{
public:
	GravityMode() 
		: shots_till_enemy_(3), lives_(2), time_(0), hit_(0) 
	{
		make_wall(vec2(-1,0), vec2(24,0));
		make_wall(vec2( 1,0), vec2(-24,0));
		make_wall(vec2(0,-1), vec2(0,34));

		player_.factory = new NormalShotFactory(phys_);

		for (int i = 0; i < 7; i++) {
			spawn_enemy();
		}
	}

	void draw() const {
		PoolMode::draw();

		if (hit_ > 0) {
			glEnable(GL_BLEND);
			glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
			glColor4f(1, 0, 0, hit_);
			glBegin(GL_QUADS);
				glVertex2f(VIEW.center.x - VIEW.dim.x, VIEW.center.y - VIEW.dim.y);
				glVertex2f(VIEW.center.x + VIEW.dim.x, VIEW.center.y - VIEW.dim.y);
				glVertex2f(VIEW.center.x + VIEW.dim.x, VIEW.center.y + VIEW.dim.y);
				glVertex2f(VIEW.center.x - VIEW.dim.x, VIEW.center.y + VIEW.dim.y);
			glEnd();
			glDisable(GL_BLEND);
		}
	}

	void step() {
		PoolMode::step();

		hit_ -= 5*DT;
		if (hit_ < 0) hit_ = 0;
		
		time_ += DT;
		
		while (shots_till_enemy_ <= 0) {
			spawn_enemy();
			shots_till_enemy_ += 3;
		}

		if (lives_ < 0) {
			MODE = new GameOverMode(vec3(0.4,0,0), time_, lives_);
			delete this;
			return;
		}
		
		int bad_balls = 0;
		for (balls_t::iterator i = balls_.begin(); i != balls_.end(); ++i) {
			if (dynamic_cast<Enemy*>(*i)) { bad_balls++; }
		}
		if (bad_balls == 0) {
			MODE = new GameOverMode(vec3(0,0,0.4), time_, lives_);
			delete this;
			return;
		}
	}

protected:
	int shots_till_enemy_;
	int lives_;
	double time_;
	double hit_;

	void draw_status_bar() const {
		PoolMode::draw_status_bar();
		
		glColor3f(0.7, 0.7, 0.7);
		for (int i = 0; i < lives_; i++) {
			double left = -2 + 2*i;
			double width = 1;
			glBegin(GL_QUADS);
				glVertex2f(left, 33.5);
				glVertex2f(left + width, 33.5);
				glVertex2f(left + width, 32.5);
				glVertex2f(left, 32.5);
			glEnd();
		}

		std::stringstream ss;
		ss << int(time_/60) << ":";
		ss.width(2);
		ss.fill('0');
		ss << int(time_)%60;
		glColor3f(1,1,1);
		glRasterPos2f(-10, 32.5);
		draw_text(ss.str());
	}

	void ball_off_screen(Ball* ball) {
		if (dynamic_cast<Enemy*>(ball)) {
			lives_--;
			hit_ = 1;
			spawn_enemy();
		}
	}

	void shoot() {
		PoolMode::shoot();
		shots_till_enemy_--;
	}
};

bool GameOverMode::events(const SDL_Event& e) {
	if (e.type == SDL_KEYDOWN || e.type == SDL_MOUSEBUTTONDOWN) {
		MODE = new GravityMode;
		delete this;
		return true;
	}
	else {
		return false;
	}
}

#endif
