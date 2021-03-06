#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <gts.h>
#include <cmath>
#include <iostream>

guint RESOLUTION = 100;
guint BAILOUT = 500;
guint EDGES = 10000;
bool REDUCE = false;

gdouble EYEX = 0, EYEY = -4, EYEZ = 0;
gdouble SLICEK = 0.1;

struct Quaternion
{
    Quaternion()
        : r(0), i(0), j(0), k(0)
    { }

    Quaternion(gdouble r, gdouble i, gdouble j, gdouble k)
        : r(r), i(i), j(j), k(k)
    { }
    
    gdouble r,i,j,k;
    
    gdouble norm2() const {
        return r*r + i*i + j*j + k*k;
    }

    gdouble norm() const {
        return sqrt(norm2());
    }
};

Quaternion operator * (const Quaternion& a, const Quaternion& b)
{
    return Quaternion
                ( a.r * b.r - a.i * b.i - a.j * b.j - a.k * b.k
                , a.r * b.i + a.i * b.r + a.j * b.k - a.k * b.j
                , a.r * b.j - a.i * b.k + a.j * b.r + a.k * b.i
                , a.r * b.k + a.i * b.j - a.j * b.i + a.k * b.r);
}

Quaternion operator * (gdouble s, const Quaternion& a) {
    return Quaternion(s*a.r, s*a.i, s*a.j, s*a.k);
}

Quaternion operator + (const Quaternion& a, const Quaternion& b)
{
    return Quaternion(a.r + b.r, a.i + b.i, a.j + b.j, a.k + b.k);
}

double quaternibrot(Quaternion z, int bailout) {
    //Quaternion c(-0.08,0.0,-0.83,-0.025);
    Quaternion c(0.08,0,0.21,-0.57);
    Quaternion zp(1,0,0,0);
    int iters = 0;
    while (true) {
        zp = 2 * z * zp;
        z = z*z + c;
        gdouble norm = z.norm2();
        if (norm > 4) {
            return z.norm() / (2*zp.norm()) * log(z.norm());
        }
        if (iters++ > bailout) {
            return -0.01;
            //return norm - 4;
            //return -z.norm() / (2*zp.norm()) * log(z.norm());
        }
    }
}

void quaternibrotFunc(gdouble** a, GtsCartesianGrid g, guint i, gpointer data)
{
    for (int x = 0; x < g.nx; x++) {
        gdouble fx = g.x + g.dx * x;
        for (int y = 0; y < g.ny; y++) {
            gdouble fy = g.y + g.dy * y;
            a[x][y] = quaternibrot(Quaternion(fx, fy, g.z, SLICEK), BAILOUT);
        }
    }
    std::cout << "\r" << gdouble(i)/g.nz << std::flush;
}

void drawVertex(GtsVertex* v)
{
    gdouble nx = 0, ny = 0, nz = 0;
    GSList* list = gts_vertex_triangles(v, NULL);
    GSList* cptr = list;
    while (cptr) {
        gdouble mnx, mny, mnz;
        gts_triangle_normal((GtsTriangle*)cptr->data, &mnx, &mny, &mnz);
        nx += mnx;  ny += mny;  nz += mnz;
        cptr = cptr->next;
    }
    g_slist_free(list);

    gdouble len = sqrt(nx*nx + ny*ny + nz*nz);
    gdouble scale = 1/len;
    glNormal3f(nx*scale, ny*scale, nz*scale);
    glVertex3f(v->p.x, v->p.y, v->p.z);
}

void drawFace(GtsFace* face)
{
    GtsVertex* v1, * v2, * v3;
    gts_triangle_vertices(&face->triangle, &v1, &v2, &v3);
    drawVertex(v1);
    drawVertex(v2);
    drawVertex(v3);
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
    glColor3f(0.3,0.2,0.6);
    glBegin(GL_TRIANGLES);
        gts_surface_foreach_face(surf, &drawFace, NULL);
    glEnd();
}

gboolean stopFunc(gdouble cost, guint nedge, gpointer data)
{
    return nedge < EDGES;
}

GtsSurface* makeSurface()
{
    GtsSurface* surf = gts_surface_new(gts_surface_class(), gts_face_class(), gts_edge_class(), gts_vertex_class());
    GtsCartesianGrid grid;
    grid.nx = grid.ny = grid.nz = RESOLUTION;
    grid.x = grid.y = grid.z = -2.0;
    grid.dx = grid.dy = grid.dz = 4.0/RESOLUTION;
    gts_isosurface_cartesian(surf, grid, &quaternibrotFunc, NULL, 0);
    if (REDUCE) gts_surface_coarsen(surf, NULL, NULL, NULL, NULL, &stopFunc, NULL, 0);
    std::cout << "\n";
    return surf;
}

gint pickFirstFace(gpointer item, gpointer data)
{
    *static_cast<gpointer*>(data) = item;
    return 1;
}

void freeSurface(GtsSurface* surf)
{
    GtsFace* first;
    gts_surface_foreach_face(surf, &pickFirstFace, static_cast<gpointer>(&first));
    gts_surface_traverse_destroy(gts_surface_traverse_new(surf, first));
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
    glMatrixMode(GL_MODELVIEW);
    glLoadIdentity();
}

void draw(bool recreate)
{
    static GtsSurface* surf = NULL;
    if (recreate) {
        if (surf) freeSurface(surf);
        surf = makeSurface();
    }
    if (!surf) return;

    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
    glLoadIdentity();
    gluLookAt(EYEX, EYEY, EYEZ, 0, 0, 0, 0, 0, 1);
    drawSurface(surf);
    SDL_GL_SwapBuffers();
}

int main()
{
    init();

    draw(true);

    SDL_Event e;
    while (SDL_WaitEvent(&e)) {
        if (e.type == SDL_KEYDOWN) {
            switch (e.key.keysym.sym) {
            case SDLK_ESCAPE: SDL_Quit(); exit(0); break;
            case SDLK_UP:     EYEY += 0.3; draw(false); break;
            case SDLK_DOWN:   EYEY -= 0.3; draw(false); break;
            case SDLK_RIGHT:  EYEX += 0.3; draw(false); break;
            case SDLK_LEFT:   EYEX -= 0.3; draw(false); break;
            case SDLK_a:      EYEZ += 0.3; draw(false); break;
            case SDLK_z:      EYEZ -= 0.3; draw(false); break;
            case SDLK_p:      RESOLUTION *= 1.5; draw(true); break;
            case SDLK_o:      RESOLUTION /= 1.5; draw(true); break;
            case SDLK_l:      BAILOUT    *= 1.5; draw(true); break;
            case SDLK_k:      BAILOUT    /= 1.5; draw(true); break;
            case SDLK_w:      SLICEK += 0.1; draw(true); break;
            case SDLK_q:      SLICEK -= 0.1; draw(true); break;
            case SDLK_m:      EDGES      *= 2; draw(true); break;
            case SDLK_n:      EDGES      /= 2; draw(true); break;
            case SDLK_r:      REDUCE = !REDUCE; draw(true); break;
            }
        }
        if (e.type == SDL_QUIT) {
            break;
        }
    }
    SDL_Quit();
}
