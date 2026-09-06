# Always-inline attributes in headers are declaration-only metadata

The allowlisted GNU spelling may appear before the return type or after the
function declarator. It does not change the checked C body semantics.

```c filename=include/always_inline_attributes.h
#ifndef ALWAYS_INLINE_ATTRIBUTES_H
#define ALWAYS_INLINE_ATTRIBUTES_H
static inline __attribute__((always_inline)) int32 increment(int32 value) {
    return value + 1;
}

static __always_inline int32 twice_increment(int32 value)
    __attribute__((__always_inline__)) {
    int32 next;
    next = increment(value);
    return increment(next);
}
#endif
```

```c filename=main.c
#include "include/always_inline_attributes.h"

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
