# An inline helper's local leaves a live caller local alone

The caller's `x` holds 1 across a helper that writes its own `x`. Claiming the
helper's value fails against the caller's, which is the one `return x` reads.

```c filename=include/hshadow.h
#ifndef HSHADOW_H
#define HSHADOW_H
static inline int32 shadow(int32 seed) {
    int32 x;
    x = seed;
    return x;
}
#endif
```

```c filename=t.c
#include "include/hshadow.h"

int32 live_local() {
    int32 x;
    int32 ignored;
    x = 1;
    ignored = shadow(99);
    return x;
}
```

```click
verifying "t.c";

int32 live_local() {
    ensures result == 99;
}
```

```expect
fail: left side evaluated to 1
```
