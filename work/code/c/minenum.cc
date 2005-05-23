#include <iostream>

using namespace std;

template <int Sz>
class MineBoard
{
public:
    MineBoard() { 
        for (int i = 0; i < Sz*Sz; i++) {
            data[i] = 0;
        }
    }
    
    bool assignable(int n) {
        bool ret = recursive_assignable<true>(0, n);
        cout << "\n";
        return ret;
    }
    
private:
    bool valid() {
        for (int i = 0; i < Sz; i++) {
            for (int j = 0; j < Sz; j++) {
                if (data[Sz*i+j]) continue;
                int ct = 0;
                if (i > 0 && j > 0)       ct += data[Sz*(i-1)+j-1];
                if (i > 0)                ct += data[Sz*(i-1)+j];
                if (i > 0 && j < Sz-1)    ct += data[Sz*(i-1)+j+1];
                if (         j > 0)       ct += data[Sz*(i)+j-1];
                                          ct += data[Sz*(i)+j];
                if (         j < Sz-1)    ct += data[Sz*(i)+j+1];
                if (i < Sz-1 && j > 0)    ct += data[Sz*(i+1)+j-1];
                if (i < Sz-1)             ct += data[Sz*(i+1)+j];
                if (i < Sz-1 && j < Sz-1) ct += data[Sz*(i+1)+j+1];
                
                if (ct > 2) return false;
            }
        }

        return true;
    }
    
    template <bool prog>
    bool recursive_assignable(int start, int numleft) {
        if (numleft == 0) {
            return valid();
        }
        for (int i = start; i < Sz*Sz - numleft; i++) {
            if (prog) cout << "#";  cout.flush();
            bool ret = false;
            data[i] = 1;
            if (recursive_assignable<false>(i+1, numleft-1)) {
                ret = true;
            }
            data[i] = 0;
            if (ret) return true;
        }
        return false;
    }
    
    char data[Sz*Sz];
};

template <int n>
void maximus() {    
    char cache[n*n] = {};
    
    int hi = n*n-1;
    int lo = 0;

    while (hi != lo) {
        int mid = (hi+lo)/2;
        if (cache[mid] == 0) {
            cout << "  (" << n << " " << mid << ")" << "\n";
            cache[mid] = MineBoard<n>().assignable(mid)+1;
        }
        if (cache[mid] - 1) {
            if (lo == mid) { 
                cout << n << ": " << lo << "\n";
                return;
            }
            lo = mid;
        }
        else {
            if (hi == mid) {
                cout << n << ": " << hi << "\n";
                return;
            }
            hi = mid;
        }
    }

    cout << n << ": " << hi << "\n";
}

int main() {
    maximus<2>();
    maximus<3>();
    maximus<4>();
    maximus<5>();
    maximus<6>();
    maximus<7>();
    maximus<8>();
    maximus<9>();
}
