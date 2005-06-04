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
const int MAXSTICK = 4;
const int ROCKMAXSTICK = 2 * MAXSTICK - 2;
const float DELAY = 1.0/100.0;
const float DAMP_THRESHOLD = 50;
const float DAMP_CONSTANT = 2;

const int A = 0, B = 1, C = 2, D = 3, E = 4, F = 5, G = 6, H = 7, R = 8;
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
    dGeomID geom;
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

int colorlist[9] = {
    0, 0,
    1, 1, 
    2, 2,
    3, 3,
    -1
};

float colorcolor[][3] = {
    { 1, 0, 0 },
    { 0, 1, 0 },
    { 0.5, 0.5, 1 },
    { 1, 1, 0 },
    { 0.5, 0, 0 },
    { 0, 0.5, 0 },
    { 0.25, 0.25, 0.5 },
    { 0.5, 0.5, 0 },
    { 1, 1, 1 }
};

void init_sdl()
{
    SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER | SDL_INIT_NOPARACHUTE);
    screen = SDL_SetVideoMode(1024, 768, 32, SDL_FULLSCREEN | SDL_OPENGL);
    
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluPerspective(45.0, 4.0/3.0, 1, 500);
    gluLookAt(50, 50, 50, 0, 0, 0, 1, 0, 0);
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

    part->geom = dCreateSphere(space, 0.2);
    dGeomSetBody(part->geom, part->body);
    part->color = color;
    dBodySetData(part->body, part);
    dGeomSetData(part->geom, part);

    if (colorlist[part->color] >= 0) {
        force_lists[colorlist[part->color]].push_back(particles.size()-1);
    }
}

double randrange(double lo, double hi) {
    return drand48() * (hi - lo) + lo;
}

int randsel(int a, int b) {
    return lrand48() % 2 ? a : b;
}

void clear_particles()
{
    force_lists = vector< vector<int> >(4);
    for (int i = 0; i < particles.size(); i++) {
        dGeomDestroy(particles[i]->geom);
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
            }
        }
    }
    Uint8* keys = SDL_GetKeyState(0);
    if (keys[SDLK_LEFT]) zrot += 90 * STEP;
    if (keys[SDLK_RIGHT]) zrot -= 90 * STEP;

    for (int i = 0; i < 9; i++) {
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

// Return what a turns b into
int basis_transform(int a, int b) 
{
    if (RCK(a) || RCK(b)) return b;
    
    switch (a) {
    case A: return b == H ? randsel(F, G) : E;
    case B: return b == G ? randsel(E, H) : F;
    case C: return b == F ? randsel(E, H) : G;
    case D: return b == E ? randsel(F, G) : H;
    case E: return b == A ? randsel(B, C) : D;
    case F: return b == B ? randsel(A, D) : C;
    case G: return b == C ? randsel(A, D) : B;
    case H: return b == D ? randsel(B, C) : A;
    }
    abort();
}

bool color_transform(int a, int b, int* ao, int* bo)
{
    if (!(LIT(a) ^ LIT(b)) || RCK(a) || RCK(b)) {
        *ao = a;
        *bo = b;
        return false;
    }

    *ao = basis_transform(b, a);
    *bo = basis_transform(a, b);
    return true;
}

bool can_stick(Particle* p1, Particle* p2)
{
    int color1 = p1->color;
    int color2 = p2->color;
    if (dBodyGetNumJoints(p1->body) > (RCK(color1) ? ROCKMAXSTICK : MAXSTICK)
      ||dBodyGetNumJoints(p2->body) > (RCK(color2) ? ROCKMAXSTICK : MAXSTICK))
        return false;
    if (RCK(color1) || RCK(color2)) return true;
    if (LIT(color1) ^ LIT(color2)) return false;
    return !(GAY(color1) ^ GAY(color2));
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
        dReal fmag = -(speed - 50) / (DAMP_CONSTANT * speed);
        dBodyAddForce(p->body, fmag * vel[0], fmag * vel[1], fmag * vel[2]);
    }
}

void step()
{
    for (int i = 0; i < particles.size(); i++) {
        damp(particles[i]);
    }

    for (int list = 0; list < force_lists.size(); list++) {
        
        for (int li = 0; li < force_lists[list].size(); li++) {
            int i = force_lists[list][li];
            
            const dReal* ipos = dBodyGetPosition(particles[i]->body);
            const dReal* ivel = dBodyGetLinearVel(particles[i]->body);
            for (int lj = 0; lj < force_lists[list].size(); lj++) {
                int j = force_lists[list][lj];

                if (i == j) continue;

                // Particles in different alignments don't interact
                if (LIT(particles[i]->color) ^ LIT(particles[j]->color)) continue;
                // Particles in different sexualities don't interact
                if (GAY(particles[i]->color) ^ GAY(particles[j]->color)) continue;

                const dReal* jpos = dBodyGetPosition(particles[j]->body);
                
                dVector3 ov;  ov[0] = jpos[0] - ipos[0];
                              ov[1] = jpos[1] - ipos[1];
                              ov[2] = jpos[2] - ipos[2];
                dReal vlen = sqrt(ov[0]*ov[0] + ov[1]*ov[1] + ov[2]*ov[2]);
                dReal div = vlen * vlen * vlen / MAG;
                dVector3 v;   v[0] = ov[0] / div;
                              v[1] = ov[1] / div;
                              v[2] = ov[2] / div;

                switch (particles[i]->color) {
                case A:  // gay particles
                case B:
                case E:
                case F:
                    if (particles[j]->color == particles[i]->color) {
                        dBodyAddForce(particles[j]->body, -v[0], -v[1], -v[2]);
                    }
                    else {
                        dBodyAddForce(particles[j]->body, v[0], v[1], v[2]);
                    }
                    break;
                case C:  // straight particles
                case D:
                case G:
                case H:
                    if (particles[j]->color == particles[i]->color) {
                        dBodyAddForce(particles[j]->body, v[0], v[1], v[2]);
                    }
                    else {
                        dBodyAddForce(particles[j]->body, -v[0], -v[1], -v[2]);
                    }
                    break;
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

void collide_callback(void* data, dGeomID g1, dGeomID g2)
{
    Particle* p1;
    Particle* p2;
    
    dContactGeom cts[1];
    int numcts = dCollide(g1, g2, 1, cts, sizeof(dContactGeom));
    if (numcts) {
        if ((p1 = (Particle*)dGeomGetData(g1)) && (p2 = (Particle*)dGeomGetData(g2))) {
            if (!color_transform(p1->color, p2->color, &p1->color, &p2->color)) {
                if (dAreConnected(p1->body, p2->body)) {
                    sanity_check(p1);
                    sanity_check(p2);
                }
                else {
                    if (!can_stick(p1, p2)) return;
                    dJointID joint = dJointCreateFixed(world, NULL);
                    dJointAttach(joint, p1->body, p2->body);
                    dJointSetFixed(joint);
                }
            }
        }
        else {
            for (int i = 0; i < numcts; i++) {
                dContact contact;
                contact.surface.mode = dContactBounce;
                contact.surface.mu = 0;
                contact.surface.bounce = 0.75;
                contact.geom = cts[0];
                dJointID joint = dJointCreateContact(world, contacts, &contact);
                dJointAttach(joint, dGeomGetBody(g1), dGeomGetBody(g2));
            }
        }
    }
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
    //space = dHashSpaceCreate(NULL);
    space = dQuadTreeSpaceCreate(NULL, center, extents, 5);

    dCreatePlane(space, 1, 0, 0, SCRLEFT);
    dCreatePlane(space, -1, 0, 0, -SCRRIGHT);
    dCreatePlane(space, 0, 1, 0, SCRBOT);
    dCreatePlane(space, 0, -1, 0, -SCRTOP);
    dCreatePlane(space, 0, 0, 1, SCRFRONT);
    dCreatePlane(space, 0, 0, -1, -SCRBACK);
    
    clear_particles();
    
    Uint32 pretime = timest = SDL_GetTicks();
    while (true) {
        while (SDL_GetTicks() - pretime < 1000 * DELAY);
        pretime = SDL_GetTicks();
        
        frames++;
        draw();
        events();
        step();

        dSpaceCollide(space, NULL, &collide_callback);
        dWorldQuickStep(world, STEP);
        dJointGroupEmpty(contacts);
    }
}
