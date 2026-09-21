# An inline helper's local is not the caller's local of that name

An inlined body runs on the caller's storage with its own names. A local it
declares is a new automatic object, so it cannot be the caller's object of the
same name. Here the caller has declared `buf` and never written it, so reading
it is a read of uninitialized storage however many times the helper wrote its
own `buf`.

```c filename=include/hstash.h
#ifndef HSTASH_H
#define HSTASH_H
static inline int32 stash(int32 seed) {
    int32 buf[2];
    buf[0] = seed;
    buf[1] = seed;
    return buf[0];
}
#endif
```

```c filename=t.c
#include "include/hstash.h"

int32 later_local() {
    int32 ignored;
    int32 buf[2];
    ignored = stash(42);
    return buf[0];
}
```

```click
verifying "t.c";

int32 later_local() {
    ensures result == 42;
}
```

```expect
fail: read of uninitialized storage
```
