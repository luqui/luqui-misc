#ifndef __PRELUDE_H__
#define __PRELUDE_H__

#include <iostream>
#include <cstdlib>

struct Val {
    virtual ~Val() { }
};

struct Closure : public Val {
    virtual ~Closure() { }
    virtual Val* call() = 0;
};

struct Int : public Val {
    Int(int d) : data(d) { }
    int data;
};

#endif
