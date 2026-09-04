# One-parameter function-like macros expand across headers

Click supports one-parameter function-like macros with ordinary argument
substitution. Arguments and replacements are rescanned for other supported
macros, while comments and quoted literals are left untouched.

```c filename=include/macros.h
#ifndef MACROS_H
#define MACROS_H
#define INCREMENT(value) ((value) + 1)
#define APPLY(value) INCREMENT(value)
#endif
```

```c filename=main.c
#include "include/macros.h"

int32 run() {
    return APPLY(4);
}

int32 nested() {
    return APPLY(INCREMENT(2));
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 5;
} by {
    execute();
    simp();
}

int32 nested() {
    ensures result == 4;
} by {
    execute();
    simp();
}
```

```expect
pass
```
