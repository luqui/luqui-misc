#include <iostream>

class BaseFoo {
public:
    virtual ~BaseFoo() { }
    virtual int get() = 0;
};

class DoneFoo : public BaseFoo {
public:
    DoneFoo(int r) : ret(r) { std::cout << "Constructing value\n"; }
    ~DoneFoo() { std::cout << "Destroying value\n"; }
    int get() {
        return ret;
    }
    int ret;
};

class ComputeFoo : public BaseFoo {
public:
    ComputeFoo() { std::cout << "Constructing computer\n"; }
    ~ComputeFoo() { std::cout << "Destroying computer!\n"; }
    int get() {
        std::cout << "Computing!\n";
        this->~ComputeFoo();
        new(this) DoneFoo(42);
        return 42;
    }
    int dummy;
};


int main() {
    BaseFoo* x = new ComputeFoo;
    std::cout << x->get() << "\n";
    std::cout << x->get() << "\n";
    std::cout << x->get() << "\n";
    delete x;
}
