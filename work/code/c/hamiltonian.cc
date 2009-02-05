#include <vector>
#include <cstdlib>
#include <cmath>
#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>

class Hamiltonian {
public:
    virtual ~Hamiltonian() { }
    
    virtual double operator() (const std::vector<double>& p, const std::vector<double>& q) const = 0;
};

class HEvolver {
public:
    HEvolver(const Hamiltonian* H, const std::vector<double>& p0, const std::vector<double>& q0)
        : hamil(H), P(p0), Q(q0)
    {
       E = (*H)(P,Q); 
    }

    void evolve(double timestep) {
        const int size = P.size();
        std::vector<double> dHdp(size);
        std::vector<double> dHdq(size);
        const Hamiltonian& H = *hamil;
        
        double h = timestep;
        for (int i = 0; i < size; i++) {
            double pi0 = P[i];
            P[i] = pi0 + h;
            double ppos = H(P,Q);
            P[i] = pi0 - h;
            double pneg = H(P,Q);
            P[i] = pi0;

            dHdp[i] = (ppos - pneg) / (2*h);


            double qi0 = Q[i];
            Q[i] = qi0 + h;
            double qpos = H(P,Q);
            Q[i] = qi0 - h;
            double qneg = H(P,Q);
            Q[i] = qi0;

            dHdq[i] = (qpos - qneg) / (2*h);
        }


        for (int i = 0; i < size; i++) {
            P[i] -= timestep * dHdq[i];
            Q[i] += timestep * dHdp[i];
        }

        double newE = H(P,Q);
        double scale = E/newE;
        for (int i = 0; i < size; i++) {
            P[i] *= scale;
            Q[i] *= scale;
        }
    }

    double operator[] (int i) const { return Q[i]; }

private:
    const Hamiltonian* hamil;
    double E;
    std::vector<double> P;
    std::vector<double> Q;
};


class Physics : public Hamiltonian {
public:
    double operator() (const std::vector<double>& p, const std::vector<double>& q) const {
        double E = 0;
        // kinetic
        E += p[0]*p[0] + p[1]*p[1];
        E += p[2]*p[2] + p[3]*p[3];

        // grav. potential
        /*
        E += q[1];
        E += q[3];
        */

        // electric potential
        E += std::sqrt((q[0]-q[2])*(q[0]-q[2]) + (q[1]-q[3])*(q[1]-q[3]));

        return E;
    }
};


HEvolver* EVOLVER;
Hamiltonian* HAMILTONIAN;

void init() {
    SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER);
    SDL_SetVideoMode(640, 480, 32, SDL_OPENGL);

    glMatrixMode(GL_PROJECTION);
    gluOrtho2D(-16, 16, -12, 12);
    glMatrixMode(GL_MODELVIEW);
}

void draw() {
    const HEvolver& e = *EVOLVER;
    glBegin(GL_POINTS);
        glVertex2f(e[0], e[1]);
        glVertex2f(e[2], e[3]);
    glEnd();
}

void step() {
    EVOLVER->evolve(1/30.0f);
}

void events() {
    SDL_Event e;
    while (SDL_PollEvent(&e)) {
        if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
            SDL_Quit();
            std::exit(0);
        }
    }
}

int main() {
    init();

    std::vector<double> i(4);
    i[0] = 0; i[1] = 0;
    i[2] = 1; i[3] = 1;

    std::vector<double> j(4);
    j[0] = -1; j[2] = 1;

    EVOLVER = new HEvolver(new Physics, j,i);

    while (true) {
        events();
        step();
        glClear(GL_COLOR_BUFFER_BIT);
        draw();
        SDL_GL_SwapBuffers();
        SDL_Delay(1000/30);
    }
}
