# Duplicate inline helpers from distinct headers are rejected

Two different headers reached from one translation unit must not define
the same `static inline` helper twice, even with identical bodies. Each
translation unit keeps its own instance, but one translation unit still
holds exactly one definition.

```c filename=include/left.h
static inline int32 helper(int32 value) { return value + 1; }
```

```c filename=include/right.h
static inline int32 helper(int32 value) { return value + 1; }
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
fail:duplicate function definition `helper`
```
