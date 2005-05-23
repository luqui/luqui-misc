#include <iostream>

#define INTLIST_1(a)        IntList<a, Null>
#define INTLIST_2(a,b)      IntList<a, INTLIST_1(b)>
#define INTLIST_3(a,b,c)    IntList<a, INTLIST_2(b,c)>
#define INTLIST_4(a,b,c,d)  IntList<a, INTLIST_3(b,c,d)>

struct Null;

template <int H, class T>
struct IntList
{
    static const int value = H;
    typedef T next;
};

template <class Sel, class V, class Child>
struct DimSelector
{
    typedef Child Type;
};

template <class V, class Child>
struct DimSelector<Null, V, Child>
{
    typedef V Type;
};

template <class V, class X>
struct Array;

template <class V, int Dim, class Tail>
struct Array< V, IntList<Dim, Tail> >
{
    typedef typename DimSelector< Tail, V, Array<V, Tail> >::Type Child;

    Child* data;

    Array() {
        data = new Child[Dim];
    }

    ~Array() {
        delete[] data;
    }

    Child& operator [] (int index) {
        return data[index];
    }
};

int main()
{
    Array<int, INTLIST_1(2)> ax;
    Array<int, INTLIST_2(2,2)> ay;

    ax[0] = 3;
    ax[1] = 4;
    
    ay[0][0] = 1;   ay[0][1] = 0;
    ay[1][0] = 0;   ay[1][1] = 1;

    std::cout << ax[0] << " " << ax[1] << "\n";
    std::cout << ay[0][0] << " " << ay[0][1] << "\n";
    std::cout << ay[1][0] << " " << ay[1][1] << "\n";
}
