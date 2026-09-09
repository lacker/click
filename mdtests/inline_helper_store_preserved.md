# Inline helper stores preserve caller-local updates

The value written through a pointer to a caller local remains visible after an
inline helper returns.

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
    ignored = set0(&n);
    return n;
}
```

```click
verifying "t.c";

int32 run_set0_local() {
    ensures result == 9;
}
```

```expect
pass
```
