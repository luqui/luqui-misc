#include <soy/init.h>
#include <soy/Viewport.h>
#include <soy/Timer.h>
#include <list>

const double DT = 1/45.0;  // This should be put in a proper place

#include "Car.h"
#include "Road.h"

SoyInit INIT;
Viewport VIEW(vec2(0,0), vec2(48, 36));

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

void init_scene() 
{
	clear_list(CARS);
	clear_list(ROADS);
	clear_list(LIGHTS);

	Light* light1, * light2;
	Road* road;

	LIGHTS.push_back(light1 = new Light(vec2(-15, 0)));
	LIGHTS.push_back(light2 = new Light(vec2(15, 0)));
	ROADS.push_back(road = new Road(light1, light2, EAST, 3));

	for (int i = 0; i < 5; i++) {
		Car* car;
		car = new Car(road, vec2(-9 - i, 0));
		car->set_comfort_distance(1);
		car->set_max_accel(1);
		CARS.push_back(car);
	}
}

void step() 
{
	for (cars_t::iterator i = CARS.begin(); i != CARS.end(); ++i) {
		(*i)->step();
	}
	for (lights_t::iterator i = LIGHTS.begin(); i != LIGHTS.end(); ++i) {
		(*i)->step();
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

int main()
{
	FrameRateLockTimer timer(DT);
	
	init();
	init_scene();

	while (true) {
		events();
		step();

		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();

		timer.lock();
	}
}
