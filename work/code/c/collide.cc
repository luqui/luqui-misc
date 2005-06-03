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
const int NUMPARTICLES = 300;
const float MAG = 600;
const float STRONGMIN = -1;
const float STRONGMAX = 0;
const float VELRANGE = 0;
const float STEP = 0.003;
const int ROCK = 8;

// colors 0-8 (9 colors)
struct Particle {
    dBodyID body;
    dGeomID geom;
    int color;
};

dWorldID world;
vector<Particle*> particles;
dSpaceID space;
dJointGroupID contacts;
Uint32 timest;
int frames = 0;
float zrot = 0;

float colorcolor[][3] = {
    { 1, 0, 0 },
    { 0, 1, 0 },
    { 0, 0, 1 },
    { 1, 1, 0 },
    { 0.5, 0, 0 },
    { 0, 0.5, 0 },
    { 0, 0, 0.5 },
    { 0.5, 0.5, 0 },
    { 1, 1, 1 }
};

void init_sdl()
{
    SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER);
//    screen = SDL_SetVideoMode(1024, 768, 32, SDL_FULLSCREEN | SDL_OPENGL);
    screen = SDL_SetVideoMode(1024, 768, 32, SDL_OPENGL);
    
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluPerspective(45.0, 4.0/3.0, 1, 500);
    gluLookAt(50, 50, 50, 0, 0, 0, 1, 0, 0);
    glMatrixMode(GL_MODELVIEW);
    glEnable(GL_DEPTH_TEST);
    glDepthFunc(GL_LEQUAL);
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
}

double randrange(double lo, double hi) {
    return drand48() * (hi - lo) + lo;
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
                    SDL_Quit();
                    exit(0);
                }
            }
        }
    }
    Uint8* keys = SDL_GetKeyState(0);
    if (keys[SDLK_LEFT]) zrot += 90 * STEP;
    if (keys[SDLK_RIGHT]) zrot -= 90 * STEP;

    static int counter = 0;
    if (keys[SDLK_SPACE]) {
        if ((++counter %= 2) == 0) {
            new_particle(0.1, 0.1, 0.1,
                         randrange(30,50), randrange(30,50), randrange(30,50),
                         5);
        }
    }
}

int basis_transform(int a, int b) 
{
    int na = a & 3;
    int nb = b & 3;

    // HAHAHAHA UNDOCUMENTED
    switch (na) {
    case 0:
        if (nb == 0 || nb == 1) return b;
        else return (lrand48() % 2) | (b & 4);
    case 1:
        if (nb == 2 || nb == 3) return b;
        else return (lrand48() % 2 + 2) | (b & 4);
    case 2:
        if (nb == 0 || nb == 3) return b;
        else return (3 * (lrand48() % 2)) | (b & 4);
    case 3:
        if (nb == 1 || nb == 2) return b;
        else return (lrand48() % 2 + 1) | (b & 4);
    }
}

bool color_transform(int a, int b, int* ao, int* bo)
{
    //if (!((a & 4) ^ (b & 4)) || a == ROCK || b == ROCK) {
    if (a < 4 && b < 4 || a >= 4 && b >= 4 || a == ROCK || b == ROCK) {
        *ao = a;
        *bo = b;
        return false;
    }

    *ao = basis_transform(b, a);
    *bo = basis_transform(a, b);
    return true;
}

// 0-1 are gay
// 2-3 are straight
// 4-5 are gay
// 6-7 are straight
// 8 is rock
void step()
{
    for (int i = 0; i < particles.size(); i++) {
        const dReal* ipos = dBodyGetPosition(particles[i]->body);
        const dReal* ivel = dBodyGetLinearVel(particles[i]->body);
        for (int j = 0; j < particles.size(); j++) {

            if (i == j) continue;
            const dReal* jpos = dBodyGetPosition(particles[j]->body);
            
            dVector3 v;  v[0] = jpos[0] - ipos[0];
                         v[1] = jpos[1] - ipos[1];
                         v[2] = jpos[2] - ipos[2];
            dReal vlen = sqrt(v[0]*v[0] + v[1]*v[1] + v[2]*v[2]);
            vlen = vlen * vlen * vlen / MAG;
            v[0] /= vlen; v[1] /= vlen; v[2] /= vlen;

            switch (particles[i]->color) {
            case 0:
            case 1:
                if (particles[j]->color != 0 && particles[j]->color != 1) break;
                if (particles[j]->color == particles[i]->color) {
                    dBodyAddForce(particles[j]->body, -v[0], -v[1], -v[2]);
                }
                else {
                    dBodyAddForce(particles[j]->body, v[0], v[1], v[2]);
                }
                break;
            case 2:
            case 3:
                if (particles[j]->color != 2 && particles[j]->color != 3) break;
                if (particles[j]->color == particles[i]->color) {
                    dBodyAddForce(particles[j]->body, v[0], v[1], v[2]);
                }
                else {
                    dBodyAddForce(particles[j]->body, -v[0], -v[1], -v[2]);
                }
            case 4:
            case 5:
                if (particles[j]->color != 4 && particles[j]->color != 5) break;
                if (particles[j]->color == particles[i]->color) {
                    dBodyAddForce(particles[j]->body, -v[0], -v[1], -v[2]);
                }
                else {
                    dBodyAddForce(particles[j]->body, v[0], v[1], v[2]);
                }
                break;
            case 6:
            case 7:
                if (particles[j]->color != 6 && particles[j]->color != 7) break;
                if (particles[j]->color == particles[i]->color) {
                    dBodyAddForce(particles[j]->body, v[0], v[1], v[2]);
                }
                else {
                    dBodyAddForce(particles[j]->body, -v[0], -v[1], -v[2]);
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
    glColor3f(1,1,1);
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
        glColor3f(color[0],color[1],color[2]);
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
            /* HINGE 
            dJointID joint = dJointCreateHinge(world, NULL)
            dJointAttach(joint, p1->body, p2->body);
            const dReal* p1pos = dBodyGetPosition(p1->body);
            const dReal* p2pos = dBodyGetPosition(p2->body);
            dJointSetHingeAnchor(joint, (p1pos[0]+p2pos[0])/2,
                                        (p1pos[1]+p2pos[1])/2,
                                        (p1pos[2]+p2pos[2])/2);
            dJointSetHingeAxis(joint, 0, 0, 1);
            // */
            
            // /* FIXED
            if (!color_transform(p1->color, p2->color, &p1->color, &p2->color)) {
                if (dAreConnected(p1->body, p2->body)) return;
                dJointID joint = dJointCreateFixed(world, NULL);
                dJointAttach(joint, p1->body, p2->body);
                dJointSetFixed(joint);
            }
        }
        else {
            for (int i = 0; i < numcts; i++) {
                dContact contact;
                contact.surface.mode = dContactBounce;
                contact.surface.mu = 0;
                contact.surface.bounce = 1;
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
    
    for (int i = 0; i < NUMPARTICLES; i++) {
        int color = lrand48() % 5;
        if (color > 3) color = 8;
        new_particle(
                randrange(SCRLEFT, SCRRIGHT),
                randrange(SCRBOT, SCRTOP),
                randrange(SCRFRONT, SCRBACK),
                randrange(-VELRANGE, VELRANGE),
                randrange(-VELRANGE, VELRANGE),
                randrange(-VELRANGE, VELRANGE),
                color);
    }

    timest = SDL_GetTicks();
    while (true) {
        frames++;
        draw();
        events();
        step();

        dSpaceCollide(space, NULL, &collide_callback);
        dWorldQuickStep(world, STEP);
        dJointGroupEmpty(contacts);
    }
}
