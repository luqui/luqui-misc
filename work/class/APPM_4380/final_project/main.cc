#include <iostream>
#include <cstdlib>
#include <list>
#include <soy/init.h>
#include <soy/Viewport.h>
#include <soy/Timer.h>
#include <soy/util.h>

const double DT = 1/45.0;  // This should be put in a proper place

#include "Car.h"
#include "Road.h"

struct LightParams {
	double ontime, offtime, phase;
};

SoyInit INIT;
Viewport VIEW(vec2(0,0), vec2(60, 45));

typedef std::list<Car*> cars_t;
cars_t CARS;
typedef std::list<Road*> roads_t;
roads_t ROADS;
typedef std::list<Light*> lights_t;
lights_t LIGHTS;

void init()
{
	INIT.init();
	VIEW.activate();
}

template <class T>
void clear_list(T& list) {
	for (typename T::iterator i = list.begin(); i != list.end(); ++i) {
		delete *i;
	}
	list.clear();
}

Road* make_road(vec2 start, Light* slight, vec2 end, Light* elight, Direction dir) 
{
	if (!slight) LIGHTS.push_back(slight = new Light(start, 1, 0, 0));
	if (!elight) LIGHTS.push_back(elight = new Light(end, 1, 0, 0));
	Road* road;
	ROADS.push_back(road = new Road(slight, elight, dir, 3));
	return road;
}

Light* make_light(vec2 pos, const LightParams& param) {
	Light* light = new Light(pos, param.ontime, param.offtime, param.phase);
	LIGHTS.push_back(light);
	return light;
}

Road* LEFT = 0;

LightParams params[2];

void init_scene() 
{
	clear_list(CARS);
	clear_list(ROADS);
	clear_list(LIGHTS);

	Road* left   = make_road(vec2(-45, 0), 0, vec2(-15, 0), 
			make_light(vec2(-15, 0), params[0]), EAST);
	Road* center = make_road(vec2(-15, 0), left->get_dest(), vec2(15, 0), 
			make_light(vec2(15, 0), params[1]), EAST);
	Road* right  = make_road(vec2(15, 0), center->get_dest(), vec2(45, 0), 0, EAST);
	LEFT = left;
}

double CARPROB = 1;

void step() 
{
	for (cars_t::iterator i = CARS.begin(); i != CARS.end(); ) {
		(*i)->step();
		if ((*i)->dead()) {
			delete *i;
			cars_t::iterator j = i++;
			CARS.erase(j);
		}
		else {
			++i;
		}
	}
	for (lights_t::iterator i = LIGHTS.begin(); i != LIGHTS.end(); ++i) {
		(*i)->step();
	}

	static double time = 0;
	static double lastcar = 0;
	time += DT;
	if (time > lastcar + 1 && randrange(0,1) < CARPROB*DT) {
		Car* car;
		car = new Car(LEFT, vec2(-44, 0));
		car->set_comfort_distance(1);
		car->set_max_accel(1);
		CARS.push_back(car);
		lastcar = time;
	}
}

void draw()
{
	for (roads_t::iterator i = ROADS.begin(); i != ROADS.end(); ++i) {
		(*i)->draw();
	}
	for (cars_t::iterator i = CARS.begin(); i != CARS.end(); ++i) {
		(*i)->draw();
	}
	for (lights_t::iterator i = LIGHTS.begin(); i != LIGHTS.end(); ++i) {
		(*i)->draw();
	}
}

void events() 
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
			INIT.quit();
			exit(0);
		}
	}
}

int main(int argc, char** argv)
{	
	if (argc != 8) {
		std::cout << "Usage: main prob on1 off1 phase1 on2 off2 phase2\n";
		return 2;
	}
	CARPROB = atof(argv[1]);
	params[0].ontime  = atof(argv[2]);
	params[0].offtime = atof(argv[3]);
	params[0].phase   = atof(argv[4]);
	params[1].ontime  = atof(argv[5]);
	params[1].offtime = atof(argv[6]);
	params[1].phase   = atof(argv[7]);
	
	
	FrameRateLockTimer timer(DT);
	
	init();
	init_scene();

	while (true) {
		events();
		step();

		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();

		//timer.lock();
	}
}
