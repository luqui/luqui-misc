#include <cstdlib>
#include <iostream>
#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>

#include "util.h"

class Screen
{
public:
    Screen() {
        SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER) == 0
                || DIE("Couldn't init SDL " + SDL_GetError());
        
        screen = SDL_SetVideoMode(800, 600, 32, SDL_OPENGL);
    }

    ~Screen() {
        SDL_Quit();
    }
private:
    SDL_Surface* screen;
};

int main()
#ifdef NDEBUG
try
#endif
{
    Screen screen;
}
#ifdef NDEBUG
catch (Exception& e) {
    std::cerr << e.msg() << std::endl;
    std::exit(1);
}
catch (...) {
    std::cerr << "Unexpected error!\n";
    std::exit(1);
}
#endif
