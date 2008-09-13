#ifndef __PRELUDE_H__
#define __PRELUDE_H__

#include <iostream>
#include <cstdlib>

struct Val {
    virtual ~Val() { }
    virtual void clone(Val*&, Val*&) = 0;
};

struct Closure : public Val {
    virtual ~Closure() { }
    virtual Val* call() = 0;
};

struct Int : public Val {
    Int(int d) : data(d) { }
    void clone(Val*& x, Val*& y) {
        x = this;
        y = new Int (data);
    }
    int data;
};

#endif
