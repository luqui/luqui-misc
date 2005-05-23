#include "Window.h"
#include <SDL_opengl.h>

Window::Window(int width, int height)
{
    SDL_Init(SDL_INIT_VIDEO);

    screen = SDL_SetVideoMode(width, height, 32, SDL_FULLSCREEN);

    glMatrixMode(GL_MODELVIEW);
}

Window::~Window()
{
    SDL_Quit();
}

void Window::set_viewport(float left, float bottom, float width, float height)
{
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluOrtho2D(left, left+width, bottom, bottom+height);
    glMatrixMode(GL_MODELVIEW);
}
