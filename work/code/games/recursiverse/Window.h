#ifndef __WINDOW_H__
#define __WINDOW_H__

#include <SDL.h>

class Window {
public:
    Window(int width, int height);
    ~Window();

    void set_viewport(float left, float bottom, float width, float height);

private:
    SDL_Surface* screen;
};

#endif
