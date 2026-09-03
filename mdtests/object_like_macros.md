# Literal object-like macros expand through shared headers

Click accepts object-like macros whose replacement is one supported integer or
character literal. Their definitions are shared with every C file that includes
the header, while the verifier analyzes the expanded translation unit.

```c filename=include/limits.h
#ifndef LIMITS_H
#define LIMITS_H
#define LIMIT 4
#define SENTINEL '\0'

int32 add_limit(int32 value);
#endif
```

```c filename=worker.c
#include "include/limits.h"

int32 add_limit(int32 value) {
    return value + LIMIT + SENTINEL;
}
```

```c filename=main.c
#include "include/limits.h"

int32 run(int32 value) {
    return add_limit(value);
}
```

```click
verifying "worker.c";
verifying "main.c";

int32 add_limit(int32 value) {
    requires value <= 2147483643;
    ensures result == value + 4;
}

int32 run(int32 value) {
    requires value <= 2147483643;
    ensures result == value + 4;
} by {
    execute();
    simp();
}
```

```expect
pass
```
