# An inline helper's local leaves a written caller array alone

The caller's `buf` already holds `v` when the helper runs, and the helper's own
`buf` is a different object, so the caller's array still holds `v` afterwards.
The claim is written for the helper's value and fails against the caller's.

```c filename=include/hstash2.h
#ifndef HSTASH2_H
#define HSTASH2_H
static inline int32 stash_arr(int32 seed) {
    int32 buf[2];
    buf[0] = seed;
    buf[1] = seed;
    return buf[0];
}
#endif
```

```c filename=t.c
#include "include/hstash2.h"

int32 inline_after_read(int32 v) {
    int32 buf[2];
    int32 got;
    buf[0] = v;
    buf[1] = v;
    got = stash_arr(5);
    return got + buf[0];
}
```

```click
verifying "t.c";

int32 inline_after_read(int32 v) {
    requires v == 1;
    ensures result == 10;
}
```

```expect
fail: left side evaluated to (5 + v)
```
