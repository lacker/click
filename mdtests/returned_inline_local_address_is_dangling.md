# A returned inline local's address is dangling

An inline helper's locals stop existing when its frame returns, so a pointer to
one of them designates no object at the call site. Reading through it is
undefined behaviour, not a way to learn what the helper wrote.

```c filename=include/hleak.h
#ifndef HLEAK_H
#define HLEAK_H
static inline int32* leak() {
    int32 z;
    z = 3;
    return &z;
}
#endif
```

```c filename=t.c
#include "include/hleak.h"

int32 use_dangling() {
    int32* q;
    q = leak();
    return *q;
}
```

```click
verifying "t.c";

int32 use_dangling() {
    ensures result == 3;
}
```

```expect
fail: invalid memory access
```
