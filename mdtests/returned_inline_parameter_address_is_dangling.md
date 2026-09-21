# A returned inline parameter's address is dangling

A by-value parameter is an automatic object of the frame it belongs to, so the
address of an inline helper's parameter is as dead after the return as the
address of one of its locals.

```c filename=include/hleakparam.h
#ifndef HLEAKPARAM_H
#define HLEAKPARAM_H
static inline int32* leak_param(int32 v) {
    return &v;
}
#endif
```

```c filename=t.c
#include "include/hleakparam.h"

int32 param_dangle() {
    int32* q;
    q = leak_param(4);
    return *q;
}
```

```click
verifying "t.c";

int32 param_dangle() {
    ensures result == 4;
}
```

```expect
fail: invalid memory access
```
