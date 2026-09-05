# Linux-style always-inline helpers are verified from included headers

The selected GNU spelling `static __always_inline` follows the same checked
body and translation-unit-local identity rules as `static inline`.

```c filename=include/always_inline.h
#ifndef ALWAYS_INLINE_HELPERS_H
#define ALWAYS_INLINE_HELPERS_H
static __always_inline int32 increment(int32 value) {
    return value + 1;
}

static __always_inline int32 twice_increment(int32 value) {
    int32 next;
    next = increment(value);
    return increment(next);
}
#endif
```

```c filename=main.c
#include "include/always_inline.h"
#include "include/always_inline.h"

int32 run() {
    return twice_increment(7);
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 9;
} by {
    execute();
    simp();
}
```

```expect
pass
```
