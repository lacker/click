# Unknown GNU function attributes are rejected

Declaration-only attributes use an explicit allowlist. Layout and other
semantic attributes need their own modeled slice.

```c filename=bad.h
static inline int32 helper(int32 value) __attribute__((aligned(8))) {
    return value;
}
```

```c filename=main.c
#include "bad.h"

int32 run() {
    return helper(1);
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 1;
}
```

```expect
fail: unsupported GNU function attribute `aligned`
```
