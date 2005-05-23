#include <iostream>
#include <complex>
#include <cstdlib>
#include <ctime>
#include <SDL.h>

using namespace std;

typedef complex<double> Complex;

#define WIDTH 640
#define HEIGHT 480
#define CAP 100

// #define CIRCLES

void events();
void buddha(const Complex& c);
void plot(const Complex& c, int count);
void update();

struct counter_entry {
    Uint16 r, g, b;
};

counter_entry counter[WIDTH][HEIGHT];

SDL_Surface* screen;

int main()
{
    srand48(time(NULL));
    
    for (int x = 0; x < WIDTH; x++) {
        for (int y = 0; y < HEIGHT; y++) {
            counter[x][y].r = counter[x][y].g = counter[x][y].b = 1;
        }
    }

    SDL_Init(SDL_INIT_VIDEO);
    screen = SDL_SetVideoMode(HEIGHT, WIDTH, 32, 0);

    int frame = 0;
    while (true) {
#ifdef CIRCLES
        Complex p(drand48() * 3 - 2, drand48() * 2 - 1);

        for (double r = 0.001; r < 0.5; r += 0.001) {
            for (double t = 0; t < 2*M_PI; t += 0.001/r) {
                buddha(Complex(r * cos(t), r * sin(t)) + p);
            }
            if (++frame % 10 == 0) {
                cout << "Frame " << frame << "\n";
                update();
            }
        }
#else
        if (++frame % 10000 == 0) {
            cout << "Frame " << frame << "\n";
            events();
            update();
        }
        Complex p(drand48() * 3 - 2, drand48() * 2 - 1);
        buddha(p);
#endif    
    }
}

void events()
{
    SDL_Event e;
    while (SDL_PollEvent(&e)) {
        if (e.type == SDL_QUIT) {
            SDL_Quit();
            exit(0);
        }
    }
}

void buddha(const Complex& c)
{
    Complex zlog[CAP];
    Complex z;
    int count = 0;

    while (count < CAP && abs(z) < 2) {
        z = z*z + c;
        zlog[count++] = z;
    }

    if (count < CAP) {
        for (int i = 1; i < count; i++) {
            plot(zlog[i], count);
        }
    }
}

void plot(const Complex& c, int count)
{
    int x = int((c.real() + 2.0) * WIDTH / 3.0);
    int y = int((c.imag() + 1.0) * HEIGHT / 2.0);
    
    if (0 <= x && x < 640 && 0 <= y && y < 480) {
        if (count < 20) {
             if (counter[x][y].r) {
                counter[x][y].r += 1;
                if (counter[x][y].r >= 512)
                    counter[x][y].r = 0;
             }
        }
        else if (count < 50) {
             if (counter[x][y].g) {
                counter[x][y].g += 1;
                if (counter[x][y].g >= 512)
                    counter[x][y].g = 0;
             }
        }
        else {
            if (counter[x][y].b) {
                counter[x][y].b += 1;
                if (counter[x][y].b >= 512)
                    counter[x][y].b = 0;
            }
        }
    }
}

void update()
{
    SDL_LockSurface(screen);
    int bpp = screen->format->BytesPerPixel;
    for (int x = 0; x < WIDTH; x++) {
        for (int y = 0; y < HEIGHT; y++) {
            Uint8* p = (Uint8*)screen->pixels + x * screen->pitch + y * bpp;
            *(Uint32*)p = SDL_MapRGB(screen->format, 
                    counter[x][y].r > 255 ? 511 - counter[x][y].r : counter[x][y].r, 
                    counter[x][y].g > 255 ? 511 - counter[x][y].g : counter[x][y].g, 
                    counter[x][y].b > 255 ? 511 - counter[x][y].b : counter[x][y].b);
        }
    }
    SDL_UnlockSurface(screen);
    SDL_UpdateRect(screen, 0, 0, 0, 0);
}
