#include <cassert>

int alias_write(int &p, const int &q) {
    p = 7;
    return q;
}

struct Guard {
    int *p;
    ~Guard() { *p = 9; }
};

int early_return(bool early, int *p) {
    Guard guard{p};
    if (early) {
        return 1;
    }
    return 2;
}

int main() {
    int value = 0;
    assert(alias_write(value, value) == 7);
    assert(early_return(true, &value) == 1);
    assert(value == 9);
    value = 0;
    assert(early_return(false, &value) == 2);
    assert(value == 9);
}
