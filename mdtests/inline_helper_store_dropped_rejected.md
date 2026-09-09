# Inline helper stores update caller locals

An inline helper included from a header executes on the caller's storage. A
store through the address of an automatic local must therefore be visible to a
later read of that local.

```c filename=include/hset.h
#ifndef HSET_H
#define HSET_H
static inline int32 set0(int32* p) {
    p[0] = 9;
    return 0;
}
#endif
```

```c filename=t.c
#include "include/hset.h"

int32 run_set0_local() {
    int32 n;
    int32 ignored;
    n = 100;
    ignored = set0(&n);
    return n;
}
```

```click
verifying "t.c";

int32 run_set0_local() {
    ensures result == 100;
}
```

```expect
fail: left side evaluated to 9
```
