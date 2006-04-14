#ifndef __NOTELIST_H__
#define __NOTELIST_H__

#include <list>
#include <cmath>
#include <SDL.h>

using std::list;

struct NoteOn {
	NoteOn(int key, int vel, float time) : key(key), vel(vel), time(time) { }
	int key;
	int vel;
	float time;
};

class NoteList {
public:
	void add_note(const NoteOn& n) { notes_.push_back(n); }

	void clear() { notes_.clear(); }

	float correlate(float dt, float offset = 0) {
		float total = 0;
		for (notes_t::iterator i = notes_.begin(); i != notes_.end(); ++i) {
			float quant = dt * round((i->time - offset) / dt) + offset;
			total += (i->time - quant)*(i->time - quant)/(dt*dt);
		}
		return total;
	}

	int size() const { return notes_.size(); }
	
private:
	typedef list<NoteOn> notes_t;
	notes_t notes_;
};

#endif
