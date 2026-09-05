# Static inline helpers are verified from included headers

Supported `static inline` definitions in a local header become ordinary C0
functions in each including translation unit. Whole-header guards still prevent
repeated inclusion from defining the helper twice.

```c filename=include/helpers.h
#ifndef INLINE_HELPERS_H
#define INLINE_HELPERS_H
static inline int32 increment(int32 value) {
    return value + 1;
}

static inline int32 twice_increment(int32 value) {
    int32 next;
    next = increment(value);
    return increment(next);
}
#endif
```

```c filename=left.c
#include "include/helpers.h"
#include "include/helpers.h"

int32 run_left() {
    return twice_increment(3);
}
```

```c filename=right.c
#include "include/helpers.h"

int32 run_right() {
    return twice_increment(4);
}
```

```click
verifying "left.c";
verifying "right.c";

int32 run_left() {
    ensures result == 5;
} by {
    execute();
    simp();
}

int32 run_right() {
    ensures result == 6;
} by {
    execute();
    simp();
}
```

```expect
pass
```
