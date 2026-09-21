# Nested inline helpers keep separate locals

One inlined helper calling another gives each frame its own `x`. The inner
helper's write cannot reach the outer helper's `x`, which still holds 7.

```c filename=include/hnest.h
#ifndef HNEST_H
#define HNEST_H
static inline int32 inner_x(int32 v) {
    int32 x;
    x = v;
    return 0;
}

static inline int32 outer_x(int32 v) {
    int32 x;
    x = 7;
    inner_x(v);
    return x;
}
#endif
```

```c filename=t.c
#include "include/hnest.h"

int32 nested_inline(int32 v) {
    return outer_x(v);
}
```

```click
verifying "t.c";

int32 nested_inline(int32 v) {
    requires v == 3;
    ensures result == 3;
}
```

```expect
fail: left side evaluated to 7
```
