# Errors inside header inline helpers point at the header

A parse diagnostic for a `static inline` helper reached through a
project-local header names the bundle header file and line, not the
including translation unit.

```c filename=include/helper.h
static inline int32 add_one(int32 value) { return value + ...; }
```

```c filename=main.c
#include "include/helper.h"

int32 run(int32 value) {
    return add_one(value);
}
```

```click
verifying "main.c";
```

```expect
fail:include/helper.h:1
```
