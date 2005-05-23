#include <iostream>

class Foo {
public:
    Foo() { }
    virtual void say() {
        std::cout << "Foo::say\n";
    }
    virtual void mutate(Foo** me);
};

class Bar : public Foo {
public:
    Bar() { }
    virtual void say() {
        std::cout << "Bar::say\n";
    }
    virtual void mutate(Foo** me) {
        // delete *me;  // to note the error
        *me = new Foo;
    }
};

void Foo::mutate(Foo** me) {
    // delete *me;
    *me = new Bar();
}

int main()
{
    Foo* foo = new Foo;
    Foo* anotherfoo = foo;

    std::cout << "foo: " << foo << "; anotherfoo: " << anotherfoo << "\n";
    foo->say();
    anotherfoo->say();

    foo->mutate(&foo);
    std::cout << "foo: " << foo << "; anotherfoo: " << anotherfoo << "\n";
    foo->say();
    anotherfoo->say();

    foo->mutate(&foo);
    std::cout << "foo: " << foo << "; anotherfoo: " << anotherfoo << "\n";
    foo->say();
    anotherfoo->say();

    return 0;
}
