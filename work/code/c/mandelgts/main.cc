#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <gts.h>
#include <cmath>
#include <iostream>

void circleFunc(gdouble** a, GtsCartesianGrid g, guint i, gpointer data)
{
    for (int x = 0; x < g.nx; x++) {
        gdouble fx = g.x + g.dx * x;
        for (int y = 0; y < g.ny; y++) {
            gdouble fy = g.y + g.dy * y;
            a[x][y] = fx*fx + fy*fy + g.z*g.z - 4;
        }
    }
}

void drawFace(GtsFace* face)
{
    gdouble nx, ny, nz;
    gts_triangle_normal(&face->triangle, &nx, &ny, &nz);
    gdouble nl = 1/sqrt(nx*nx + ny*ny + nz*nz);
    glNormal3f(nx*nl, ny*nl, nz*nl);
    
    GtsVertex* v1, * v2, * v3;
    gts_triangle_vertices(&face->triangle, &v1, &v2, &v3);
    glVertex3f(v1->p.x, v1->p.y, v1->p.z);
    glVertex3f(v2->p.x, v2->p.y, v2->p.z);
    glVertex3f(v3->p.x, v3->p.y, v3->p.z);
}

int FACES = 0;
gint drawFace(gpointer item, gpointer data)
{
    GtsFace* face = static_cast<GtsFace*>(item);
    drawFace(face);
    FACES++;
    return 0;
}

void drawSurface(GtsSurface* surf)
{
    glColor3f(1,1,1);
    glBegin(GL_LINES);
        gts_surface_foreach_face(surf, &drawFace, NULL);
    glEnd();
}


GtsSurface* makeSphere()
{
    GtsSurface* surf = gts_surface_new(gts_surface_class(), gts_face_class(), gts_edge_class(), gts_vertex_class());
    GtsCartesianGrid grid;
    grid.nx = grid.ny = grid.nz = 50;
    grid.x = grid.y = grid.z = -4.0;
    grid.dx = grid.dy = grid.dz = 8.0/50;
    gts_isosurface_cartesian(surf, grid, &circleFunc, NULL, 0);
    return surf;
}

void init()
{
    SDL_Init(SDL_INIT_VIDEO);
    SDL_SetVideoMode(640, 480, 32, SDL_OPENGL);

    glEnable(GL_DEPTH_TEST);
    glDepthFunc(GL_LEQUAL);
    
    glEnable(GL_LIGHTING);
    glEnable(GL_COLOR_MATERIAL);

    float ambient_light[] = { 0.5, 0.5, 0.5, 1 };
    float diffuse_light[] = { 0.75, 0.75, 0.75, 1 };
    float light_pos[]     = { 3, -8, 3, 1 };

    glLightfv(GL_LIGHT1, GL_AMBIENT, ambient_light);
    glLightfv(GL_LIGHT1, GL_DIFFUSE, diffuse_light);
    glLightfv(GL_LIGHT1, GL_POSITION, light_pos);

    glEnable(GL_LIGHT1);
    
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluPerspective(45.0, 4.0/3.0, 0.1, 100.0);
    gluLookAt(0, -8, 0, 0, 0, 0, 0, 0, 1);
    glMatrixMode(GL_MODELVIEW);
    glLoadIdentity();
}

int main()
{
    init();

    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
    GtsSurface* sphere = makeSphere();
    drawSurface(sphere);
    std::cout << "Drew " << FACES << " faces\n";
    SDL_GL_SwapBuffers();

    SDL_Delay(2000);
    SDL_Quit();
}
