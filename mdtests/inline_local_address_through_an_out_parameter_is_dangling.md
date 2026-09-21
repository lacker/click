# An inline local's address through an out parameter is dangling

The escape does not have to be the return value. A helper that stores the
address of its own local through a caller-supplied pointer leaves the caller
holding a pointer to storage whose lifetime ended with the helper's frame.

```c filename=include/hleakout.h
#ifndef HLEAKOUT_H
#define HLEAKOUT_H
static inline void leak_out(int32** out) {
    int32 z;
    z = 3;
    *out = &z;
}
#endif
```

```c filename=t.c
#include "include/hleakout.h"

int32 out_param_dangle() {
    int32* q;
    leak_out(&q);
    return *q;
}
```

```click
verifying "t.c";

int32 out_param_dangle() {
    ensures result == 3;
}
```

```expect
fail: invalid memory access
```
