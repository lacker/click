# Conflicting inline helpers from distinct headers are rejected

Two different headers reached from one translation unit must not declare
the same helper with different signatures. Guarded repeated inclusion of
one shared header stays accepted; this fixture covers the genuine
conflict, which names the second definition site.

```c filename=include/left.h
static inline int32 helper(int32 value) { return value + 1; }
```

```c filename=include/right.h
static inline uint8 helper(uint8 value) { return value + 1; }
```

```c filename=main.c
#include "include/left.h"
#include "include/right.h"

int32 run(int32 value) {
    return helper(value);
}
```

```click
verifying "main.c";
```

```expect
fail:conflicting declarations for function `helper`
```
