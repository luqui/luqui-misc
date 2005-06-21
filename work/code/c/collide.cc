/* THE ELEMENTARY PARTICLE TABLE
 *
 *         +-------------------------------------------+
 *         |        GAY          |        STR          |
 *         +---------------------+---------------------+
 *         |    POS   |   NEG    |    POS   |   NEG    |
 * +-------+----------+----------+----------+----------+
 * |       |    A     |     B    |     C    |    D     |
 * |  LIT  | F,G -> E | E,H -> F | E,H -> G | F,G -> H |
 * |       | H -> F|G | G -> E|H | F -> E|H | E -> F|G |
 * +-------+----------+----------+----------+----------+
 * |       |    E     |     F    |     G    |    H     |
 * |  DRK  | B,C -> D | A,D -> C | A,D -> B | B,C -> A |
 * |       | A -> B|C | B -> A|D | C -> A|D | D -> B|C |
 * +-------+----------+----------+----------+----------+
 *
 * LIT, DRK (bit 2) are the types of ALIGNMENT
 * GAY, STR (bit 1) are the types of SEXUALITY
 * POS, NEG (bit 0) are the types of CHARGE
 */ 

#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <stdlib.h>
#include <time.h>
#include <ode/ode.h>
#include <iostream>
#include <math.h>
#include <deque>
#include <vector>

using std::deque;
using std::vector;

SDL_Surface* screen;

const float SCRLEFT  = 0;
const float SCRRIGHT = 30;
const float SCRBOT   = 0;
const float SCRTOP   = 30;
const float SCRFRONT = 0;
const float SCRBACK  = 30;
const int NUMPARTICLES = 0;
const float MAG = 600;
const float STRONGMIN = -1;
const float STRONGMAX = 0;
const float VELRANGE = 20;
const float STEP = 0.003;
const int MAXSTICK = 10;
const int ROCKMAXSTICK = 2 * MAXSTICK - 2;
const float DELAY = 1.0/100.0;
const float DAMP_THRESHOLD = 0;
const float DAMP_CONSTANT = 1;

const int A = 0, B = 1, C = 2;
#define LIT(x) (!((x) & 4))
#define DRK(x) (!LIGHT(x))
#define GAY(x) (!((x) & 2))
#define STR(x) (!GAY(x))
#define POS(x) (!((x) & 1))
#define NEG(x) (!POS(x))
#define RCK(x) ((x) == 8)


// colors 0-8 (9 colors)
struct Particle {
    dBodyID body;
    int color;
};

dWorldID world;
vector<Particle*> particles;
vector< vector<int> > force_lists;
dSpaceID space;
dJointGroupID contacts;
Uint32 timest;
int frames = 0;
float zrot = 0;
bool interact_q = true;

int colorlist[3] = {
    0, 0, 0
};

float colorcolor[][3] = {
    { 1, 0, 0 },
    { 0, 0.5, 1 },
    { 1, 1, 1 }
};

void init_sdl()
{
    SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER | SDL_INIT_NOPARACHUTE);
    screen = SDL_SetVideoMode(1024, 768, 32, SDL_FULLSCREEN | SDL_OPENGL);
    
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluPerspective(45.0, 4.0/3.0, 1, 500);
    gluLookAt(60, 60, 60, 0, 0, 0, 1, 0, 0);
    glMatrixMode(GL_MODELVIEW);
    glEnable(GL_DEPTH_TEST);
    glDepthFunc(GL_LEQUAL);
    SDL_ShowCursor(0);
}

void new_particle(float x, float y, float z, float vx, float vy, float vz, int color)
{
    particles.push_back(new Particle);
    Particle* part = particles.back();
    part->body = dBodyCreate(world);
    dBodySetPosition(part->body, x, y, z);
    dBodySetLinearVel(part->body, vx, vy, vz);

    part->color = color;
    dBodySetData(part->body, part);

    if (colorlist[part->color] >= 0) {
        force_lists[colorlist[part->color]].push_back(particles.size()-1);
    }
}

double drand() {
    return double(rand() % RAND_MAX) / RAND_MAX;
}

double randrange(double lo, double hi) {
    return drand() * (hi - lo) + lo;
}

int randsel(int a, int b) {
    return rand() % 2 ? a : b;
}

void clear_particles()
{
    force_lists = vector< vector<int> >(1);
    for (int i = 0; i < particles.size(); i++) {
        dBodyDestroy(particles[i]->body);
        delete particles[i];
    }
    particles.clear();
}

void events()
{
    SDL_Event e;
    while (SDL_PollEvent(&e)) {
        switch (e.type) {
            case SDL_KEYDOWN: {
                if (e.key.keysym.sym == SDLK_ESCAPE) {
                    double dtime = (SDL_GetTicks() - timest) / 1000;
                    std::cout << "FPS: " << frames / dtime << "\n";
                    clear_particles();
                    SDL_Quit();
                    exit(0);
                }
                else if (e.key.keysym.sym == SDLK_c) {
                    clear_particles();
                }
                else if (e.key.keysym.sym == SDLK_i) { 
                    interact_q = !interact_q;
                }
            }
        }
    }
    Uint8* keys = SDL_GetKeyState(0);
    if (keys[SDLK_LEFT]) zrot += 90 * STEP;
    if (keys[SDLK_RIGHT]) zrot -= 90 * STEP;

    for (int i = 0; i < 3; i++) {
        if (SDL_GetModState() & KMOD_CTRL) {
            if (frames % 20 != 0) {
                continue;
            }
        }
        if (keys[SDLK_KP0 + i]) {
            if (keys[SDLK_SPACE]) {
                new_particle(0.1, 0.1, 0.1,
                             randrange(30,50), randrange(30,50), randrange(30,50),
                             i);
            }
            else {
                new_particle(
                        randrange(SCRLEFT, SCRRIGHT),
                        randrange(SCRBOT, SCRTOP),
                        randrange(SCRFRONT, SCRBACK),
                        randrange(-VELRANGE, VELRANGE),
                        randrange(-VELRANGE, VELRANGE),
                        randrange(-VELRANGE, VELRANGE),
                        i);
            }
            std::cout << "Number of particles: " << particles.size() << "\n";
        }
    }
}

bool can_stick(Particle* p1, Particle* p2)
{
    int color1 = p1->color;
    int color2 = p2->color;
    if (dBodyGetNumJoints(p1->body) > (RCK(color1) ? ROCKMAXSTICK : MAXSTICK)
      ||dBodyGetNumJoints(p2->body) > (RCK(color2) ? ROCKMAXSTICK : MAXSTICK))
        return false;
    if (RCK(color1) || RCK(color2)) return false;
    if (LIT(color1) ^ LIT(color2)) return false;
    if (GAY(color1) ^ GAY(color2)) return false;
    return GAY(color1) ^ POS(color1) ^ POS(color2);
}

void sanity_check(Particle* p)
{
    dBodyID body = p->body;
    int numjs = dBodyGetNumJoints(body);
    
    dJointID* destroy_joints = new dJointID [numjs];
    int num_destroy_joints = 0;

    for (int i = 0; i < numjs; i++) {
        dJointID joint = dBodyGetJoint(body, i);
        if (dJointGetType(joint) == dJointTypeContact) continue;

        if (numjs > MAXSTICK && i < numjs - MAXSTICK) {
            destroy_joints[num_destroy_joints++] = joint;
            continue;
        }
        
        dBodyID ba = dJointGetBody(joint, 0);
        dBodyID bb = dJointGetBody(joint, 1);
        Particle* dudea = (Particle*)dBodyGetData(ba);
        Particle* dudeb = (Particle*)dBodyGetData(bb);
        if (!can_stick(dudea, dudeb)) {
            destroy_joints[num_destroy_joints++] = joint;
        }
    }

    for (int i = 0; i < num_destroy_joints; i++) {
        dJointDestroy(destroy_joints[i]);
    }
    delete[] destroy_joints;
}

void damp(Particle* p)
{
    const dReal* vel = dBodyGetLinearVel(p->body);
    dReal speed = sqrt(vel[0]*vel[0] + vel[1]*vel[1] + vel[2]*vel[2]);
    if (speed > DAMP_THRESHOLD) {
        dReal fmag = -(speed - DAMP_THRESHOLD) / (DAMP_CONSTANT * speed);
        dBodyAddForce(p->body, fmag * vel[0], fmag * vel[1], fmag * vel[2]);
    }
}

void step()
{
    for (int i = 0; i < particles.size(); i++) {
        damp(particles[i]);
    }
    
    if (!interact_q) return;

    for (int list = 0; list < force_lists.size(); list++) {
        
        for (int li = 0; li < force_lists[list].size(); li++) {
            int i = force_lists[list][li];
            
            const dReal* ipos = dBodyGetPosition(particles[i]->body);
            const dReal* ivel = dBodyGetLinearVel(particles[i]->body);
            for (int lj = 0; lj < force_lists[list].size(); lj++) {
                int j = force_lists[list][lj];

                if (i == j) continue;

                const dReal* jpos = dBodyGetPosition(particles[j]->body);
                
                dVector3 ov;  ov[0] = jpos[0] - ipos[0];
                              ov[1] = jpos[1] - ipos[1];
                              ov[2] = jpos[2] - ipos[2];
                dReal r = sqrt(ov[0]*ov[0] + ov[1]*ov[1] + ov[2]*ov[2]);
                dReal scale = 0;

                static const dReal AA_MAG = 1 * MAG;
                static const dReal AB_MAG = 0.2 * MAG;
                static const dReal AB_PARAM = 2;
                static const dReal AB_R = 10;
                static const dReal AC_MAG = 1 * MAG;
                static const dReal AC_R = 0.5;
                static const dReal BB_MAG = AA_MAG;
                
                int icolor = particles[i]->color;
                int jcolor = particles[j]->color;
                if (icolor > jcolor) {
                    int tmp = icolor;
                    icolor = jcolor;
                    jcolor = tmp;
                }
                
                switch (icolor) {
                case A: 
                    if (jcolor == A) {
                        scale = AA_MAG / (r*r);
                    }
                    else if (jcolor == B) {
                        const dReal rs = 2 / (AB_PARAM * AB_R);
                        scale = -AB_MAG * (AB_PARAM / (rs*rs*r*r) - 2 / (rs*rs*rs*r*r*r));
                    }
                    else if (jcolor == C) {
                        scale = AC_MAG * (-cos(M_PI * r / AC_R) / (r*r)
                                         - M_PI * sin(M_PI * r / AC_R) / (AC_R * r));
                    }
                    break;
                case B:
                    if (jcolor == B) {
                        scale = BB_MAG / (r*r);
                    }
                    break;
                }
                
                if (scale != 0) {
                    ov[0] = scale * ov[0] / r;
                    ov[1] = scale * ov[1] / r;
                    ov[2] = scale * ov[2] / r;

                    dBodyAddForce(particles[j]->body, ov[0], ov[1], ov[2]);
                }
            }
        }
    }
}

void draw()
{
    //glClearColor(0.25, 0.25, 0.25, 0);
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
    glLoadIdentity();
    glRotatef(zrot, 1, 0, 0);
    glColor3f(0.5,0.5,0.5);
    glBegin(GL_LINES);
        glVertex3f(SCRLEFT, SCRBOT, SCRFRONT);
        glVertex3f(SCRRIGHT, SCRBOT, SCRFRONT);
        glVertex3f(SCRLEFT, SCRBOT, SCRFRONT);
        glVertex3f(SCRLEFT, SCRTOP, SCRFRONT);
        glVertex3f(SCRLEFT, SCRBOT, SCRFRONT);
        glVertex3f(SCRLEFT, SCRBOT, SCRBACK);
    glEnd();
    glPointSize(2.0);
    glBegin(GL_POINTS);
    for (int i = 0; i < particles.size(); i++) {
        const dReal* pos = dBodyGetPosition(particles[i]->body);
        float* color = colorcolor[particles[i]->color];
        glColor3f(color[0], color[1], color[2]);
        glVertex3f(pos[0], pos[1], pos[2]);
    }
    glEnd();
    SDL_GL_SwapBuffers();
}

int main()
{
    init_sdl();

    srand48(time(NULL));
    
    world = dWorldCreate();
    contacts = dJointGroupCreate(0);

    dVector3 center;  center[0]  = (SCRLEFT + SCRRIGHT) / 2;
                      center[1]  = (SCRBOT + SCRTOP) / 2;
                      center[2]  = 0;
    dVector3 extents; extents[0] = SCRRIGHT - SCRLEFT;
                      extents[1] = SCRTOP - SCRBOT;
                      extents[2] = 2;

    // /* BOUNDARY
    dCreatePlane(space, 1, 0, 0, SCRLEFT);
    dCreatePlane(space, -1, 0, 0, -SCRRIGHT);
    dCreatePlane(space, 0, 1, 0, SCRBOT);
    dCreatePlane(space, 0, -1, 0, -SCRTOP);
    dCreatePlane(space, 0, 0, 1, SCRFRONT);
    dCreatePlane(space, 0, 0, -1, -SCRBACK);
    // */
    
    clear_particles();
    
    Uint32 pretime = timest = SDL_GetTicks();
    while (true) {
        while (SDL_GetTicks() - pretime < 1000 * DELAY);
        pretime = SDL_GetTicks();
        
        frames++;
        draw();
        events();
        step();

        dWorldQuickStep(world, STEP);
        dJointGroupEmpty(contacts);
    }
}
