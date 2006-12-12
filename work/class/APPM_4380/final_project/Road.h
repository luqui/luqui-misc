#ifndef __ROAD_H__
#define __ROAD_H__

#include <soy/vec2.h>
#include <map>
#include <list>

class Car;
class Road;

enum Direction {
	NORTH, SOUTH, EAST, WEST
};
const int N_DIRECTIONS = 4;

inline vec2 to_dir(Direction d) {
	switch (d) {
		case NORTH: return vec2(0,1);
		case SOUTH: return vec2(0,-1);
		case EAST:  return vec2(1,0);
		case WEST:  return vec2(-1,0);
	}
}

inline Direction opposite_dir(Direction d) {
	switch (d) {
		case NORTH: return SOUTH;
		case SOUTH: return NORTH;
		case EAST:  return WEST;
		case WEST:  return EAST;
	}
}

class Light {
public:
	Light(vec2 pos) : roads_(), pos_(pos) { }

	vec2 get_position() const {
		return pos_;
	}
	
	void set_road(Direction d, Road* road) { 
		roads_[d] = road;
	}

	Road* get_road(Direction d) const {
		return roads_[d];
	}

	bool green(Direction from, Direction to) {
		// XXX stub
		return false;
	}
	
	void step() { }
	void draw() const { }

private:
	Road* roads_[N_DIRECTIONS];
	vec2 pos_;
};

class Road {
public:
	Road(Light* src, Light* dest, Direction dir, double speed_limit) 
		: src_(src), dest_(dest), dir_(dir), speed_limit_(speed_limit) { }

	Light* get_src()  const { return src_; }
	Light* get_dest() const { return dest_; }
	Direction get_direction_id() const { return dir_; }
	vec2 get_direction() const {
		return to_dir(get_direction_id());
	}

	double get_speed_limit() const {
		return speed_limit_;
	}
	
	const Car* get_next_car(Car* in) const {
		carmap_t::const_iterator m = carmap_.find(in);
		if (m != carmap_.end()) {
			cars_t::const_iterator i = m->second;
			++i;
			if (i != cars_.end()) {
				return *i;
			}
		}
		return 0;
	}

	const Car* get_prev_car(Car* in) const {
		carmap_t::const_iterator m = carmap_.find(in);
		if (m != carmap_.end()) {
			cars_t::const_iterator i = m->second;
			if (i != cars_.begin()) {
				--i;
				return *i;
			}
		}
		return 0;
	}

	void insert_car(Car* in) {
		cars_.push_front(in);
		carmap_.insert(std::make_pair(in, cars_.begin()));
	}

	void delete_car(Car* in) {
		carmap_t::iterator m = carmap_.find(in);
		if (m != carmap_.end()) {
			cars_t::iterator i = m->second;
			cars_.erase(i);
			carmap_.erase(m);
		}
		else {
			DIE("Cannot delete car because it was not on the road!");
		}
	}
	
	void draw() const {
		vec2 src = src_->get_position();
		vec2 dest = dest_->get_position();
		glColor3f(0.7, 0.7, 0.7);
		if (dir_ == NORTH || dir_ == SOUTH) {
			glBegin(GL_QUADS);
				glVertex2f(src.x  - 0.6, src.y);
				glVertex2f(src.x  + 0.6, src.y);
				glVertex2f(dest.x + 0.6, dest.y);
				glVertex2f(dest.x - 0.6, dest.y);
			glEnd();
		}
		else {
			glBegin(GL_QUADS);
				glVertex2f(src.x,  src.y  - 0.6);
				glVertex2f(src.x,  src.y  + 0.6);
				glVertex2f(dest.x, dest.y + 0.6);
				glVertex2f(dest.x, dest.y - 0.6);
			glEnd();
		}
	}
	
private:
	Light* const src_;
	Light* const dest_;
	const Direction dir_;
	const double speed_limit_;

	typedef std::list<Car*> cars_t;
	typedef std::map<Car*, cars_t::iterator> carmap_t;
	cars_t cars_;
	carmap_t carmap_;
};

#endif
