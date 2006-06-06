#include "physics.h"

dWorldID WORLD;
num OVERSTEP;
const num STEP = 0.01;

void init_ode()
{
	WORLD = dWorldCreate();
	dWorldSetGravity(WORLD, 0, -1, 0);
}
