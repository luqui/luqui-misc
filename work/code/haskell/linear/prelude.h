#ifndef __PRELUDE_H__
#define __PRELUDE_H__

#include <iostream>
#include <cstdlib>

struct Val {
    virtual ~Val() { }
    virtual void clone(Val*&, Val*&) = 0;
    virtual void destroy() = 0;
};

struct Closure : public Val {
    virtual ~Closure() { }
    virtual Val* call(Val*) = 0;
};

struct Int : public Val {
    Int(int d) : data(d) { }
    void clone(Val*& x, Val*& y) {
        x = this;
        y = new Int (data);
    }
    void destroy() { delete this; }
    int getdata() {
        int r = data;
        delete this;
        return r;
    }
private:
    int data;
};


struct TSplitClosure2 : public Closure {
    TSplitClosure2(Val* arg) : arg(arg) { }
    void clone(Val*& _L, Val*& _R) {
        Val* arg1; Val* arg2;
        arg->clone(arg1,arg2);
        arg = arg1;
        _L = this;
        _R = new TSplitClosure2(arg2);
    }
    void destroy() { arg->destroy(); delete this; }
    Val* call(Val* fun) {
        Val* arg1; Val* arg2;
        arg->clone(arg1,arg2);
        Val* r = ((Closure*)((Closure*)fun)->call(arg1))->call(arg2);
        delete this;
        return r;
    }
private:
    Val* arg;
};

struct TSplitClosure : public Closure {
    void clone(Val*& a, Val*& b) {
        a = this;
        b = this;
    }
    void destroy() { }
    Val* call(Val* arg) {
        return new TSplitClosure2(arg);
    }
};

TSplitClosure* SPLIT = new TSplitClosure;



struct TDestroyClosure2 : public Closure {
    TDestroyClosure2(Val* arg) : arg(arg) { }
    void clone(Val*& _L, Val*& _R) {
        Val* arg1; Val* arg2;
        arg->clone(arg1,arg2);
        arg = arg1;
        _L = this;
        _R = new TSplitClosure2(arg2);
    }
    void destroy() { arg->destroy(); delete this; }
    Val* call(Val* fun) {
        arg->destroy();
        delete this;
        return fun;
    }
private:
    Val* arg;
};

struct TDestroyClosure : public Closure {
    void clone(Val*& a, Val*& b) {
        a = this;
        b = this;
    }
    void destroy() { }
    Val* call(Val* arg) {
        return new TDestroyClosure2(arg);
    }
};

TDestroyClosure* DESTROY = new TDestroyClosure;

#endif
