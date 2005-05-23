#ifndef __SETUP_H__
#define __SETUP_H__

#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <cmath>
#include <cstdlib>
#include "ode/ode.h"

SDL_Surface* screen;

bool is_3d = false;

void init_gfx() {
    SDL_Init(SDL_INIT_VIDEO);
    screen = SDL_SetVideoMode(1024, 768, 32, SDL_OPENGL | SDL_HWSURFACE);

    glClear(GL_COLOR_BUFFER_BIT);
}

void init_2d() {
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluOrtho2D(-8, 8, -6, 6);
    glMatrixMode(GL_MODELVIEW);
    glLoadIdentity();
}

void init_3d() {
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluPerspective(45.0, 4.0/3.0, 1.0, 100.0);

    static const float ambient0[4] = {0.8, 0.8, 0.8, 1};
    static const float diffuse0[4] = {0.8, 0.8, 0.8, 1};
    static const float specular0[4] = {0, 0, 100, 1};
    static const float position0[4] = {10, 10, 10};
    glLightfv(GL_LIGHT0, GL_AMBIENT, ambient0);
    glLightfv(GL_LIGHT0, GL_DIFFUSE, diffuse0);
    glLightfv(GL_LIGHT0, GL_SPECULAR, specular0);
    glLightfv(GL_LIGHT0, GL_POSITION, position0);

    glEnable(GL_LIGHTING);
    glEnable(GL_LIGHT0);

    glEnable(GL_DEPTH_TEST);
    glDepthFunc(GL_LEQUAL);

    glEnable(GL_NORMALIZE);
    
    glMatrixMode(GL_MODELVIEW);
    glLoadIdentity();

    is_3d = true;
}

void step() {
    SDL_Event e;
    while (SDL_PollEvent(&e)) {
        switch (e.type) {
        case SDL_KEYDOWN:
            if (e.key.keysym.sym == SDLK_ESCAPE) {
                SDL_Quit();
                exit(0);
            }
            break;
        }
    }

    SDL_GL_SwapBuffers();
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
    glLoadIdentity();

    if (is_3d) {
        gluLookAt(10, 10, 10,
                  0, 0, 0,
                  0, 1, 0);
    }

}

void draw_circle() {
    glColor3f(1,1,1);
    
    glBegin(GL_TRIANGLE_FAN);
        glVertex2f(0,0);
        for (float th = 0; th <= 2 * M_PI; th += 2 * M_PI / 24) {
            glVertex2f(cos(th), sin(th));
        }
    glEnd();

    glColor3f(0,0,0);
    glBegin(GL_LINES);
        glVertex2f(0,0);
        glVertex2f(1,0);
    glEnd();
}

void draw_box() {
    glColor3f(1,1,1);

    glBegin(GL_QUADS);
        // left face
        glNormal3f(-1,  0,  0);
        glVertex3f(-1, -1, -1);
        glVertex3f(-1, -1,  1);
        glVertex3f(-1,  1,  1);
        glVertex3f(-1,  1, -1);

        // right face
        glNormal3f( 1,  0,  0);
        glVertex3f( 1, -1, -1);
        glVertex3f( 1, -1,  1);
        glVertex3f( 1,  1,  1);
        glVertex3f( 1,  1, -1);

        // bottom face
        glNormal3f( 0, -1,  0);
        glVertex3f(-1, -1, -1);
        glVertex3f(-1, -1,  1);
        glVertex3f( 1, -1,  1);
        glVertex3f( 1, -1, -1);

        // top face
        glNormal3f( 0,  1,  0);
        glVertex3f(-1,  1, -1);
        glVertex3f(-1,  1,  1);
        glVertex3f( 1,  1,  1);
        glVertex3f( 1,  1, -1);

        // back face
        glNormal3f( 0,  0, -1);
        glVertex3f(-1, -1, -1);
        glVertex3f(-1,  1, -1);
        glVertex3f( 1,  1, -1);
        glVertex3f( 1, -1, -1);
        
        // front face
        glNormal3f( 0,  0,  1);
        glVertex3f(-1, -1,  1);
        glVertex3f(-1,  1,  1);
        glVertex3f( 1,  1,  1);
        glVertex3f( 1, -1,  1);
    glEnd();
}

dReal get_q_angle(const dQuaternion q)
{
    return 2 * acos(q[0]);
}

const double EPSILON = 0.0005;

const dReal* get_q_axis(const dQuaternion q)
{
    static dVector3 v;
    double sina;

    sina = sqrt(1 - q[0]*q[0]);
    if (fabs(sina) < EPSILON) {
        sina = 1;
    }

    v[0] = q[1] / sina;
    v[1] = q[2] / sina;
    v[2] = q[3] / sina;
    return v;
}

#endif
