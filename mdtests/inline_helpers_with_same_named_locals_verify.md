# Inline helpers with same-named locals verify

Separate identities are not separate meanings: a helper called twice beside a
caller local of the same name, and a helper whose callee reuses the name again,
compute exactly what the source says.

```c filename=include/hsame.h
#ifndef HSAME_H
#define HSAME_H
static inline int32 twice_same(int32 v) {
    int32 t;
    t = v + 1;
    return t;
}

static inline int32 sum_helper(int32 a, int32 b) {
    int32 t;
    t = a + b;
    return t;
}

static inline int32 use_sum(int32 v) {
    int32 t;
    t = sum_helper(v, 1);
    return t + 1;
}
#endif
```

```c filename=t.c
#include "include/hsame.h"

int32 good_repeated(int32 v) {
    int32 t;
    int32 a;
    int32 b;
    t = 100;
    a = twice_same(v);
    b = twice_same(a);
    return t + a + b;
}

int32 good_nested(int32 v) {
    int32 t;
    t = use_sum(v);
    return t;
}
```

```click
verifying "t.c";

int32 good_repeated(int32 v) {
    requires v == 1;
    ensures result == 105;
}

int32 good_nested(int32 v) {
    requires v == 1;
    ensures result == 3;
}
```

```expect
pass
```
