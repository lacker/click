# Always-inline header definitions require internal linkage

The GNU always-inline marker does not by itself provide the internal linkage
needed for a header body in this supported slice.

```c filename=bad.h
__always_inline int32 hidden() {
    return 1;
}
```

```c filename=main.c
#include "bad.h"

int32 run() {
    return hidden();
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 1;
}
```

```expect
fail: inline function definitions in headers require `static inline` or `static __always_inline`
```
