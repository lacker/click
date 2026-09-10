# Sidecar contracts use the source name of a header-inline helper

The execution identity of a `static inline` definition is translation-unit
local, but a sidecar contract names the C function with its ordinary spelling.

```c filename=include/helper.h
#ifndef HELPER_H
#define HELPER_H
static inline int32 add_one(int32 value) {
    return value + 1;
}
#endif
```

```c filename=main.c
#include "include/helper.h"

int32 run() {
    return add_one(4);
}
```

```click
verifying "main.c";

int32 add_one(int32 value) {
    requires value < 2147483647;
    ensures result == value + 1;
} by {
    execute();
    simp();
}

int32 run() {
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
pass
```
