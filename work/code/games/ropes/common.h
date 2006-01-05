#ifndef __COMMON_H__
#define __COMMON_H__

#include "ode/ode.h"
#include <SDL/SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>

#include <cstdlib>
#include <cmath>
#include <iostream>
#include <string>

#include "tweak.h"

using namespace std;

typedef double num;

inline void quit() {
    SDL_Quit();
    exit(0);
}

inline int _die(const string& msg, char* file, int line) {
    cout << msg << " at " << file << " line " << line << endl;
    quit();
    return 0;
}

#define DIE(msg) _die(string() + msg, __FILE__, __LINE__)

// This mod is faster than fmod when |x/n| is close to 1.
// But more importantly, it takes the modulus rounding toward
// negative infinity, not toward zero like fmod. 
inline num smallmod(num x, num n) {
    while (x < 0) x += n;
    while (x >= n) x -= n;
    return x;
}

inline num sign(num x) {
    return x >= 0 ? 1 : -1;
}

#endif
