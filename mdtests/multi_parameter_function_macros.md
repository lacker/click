# Multi-parameter function-like macros expand across headers

Click supports bounded function-like macros with up to three named parameters.
Arguments may contain nested calls or parenthesized expressions, and the
replacement is rescanned for other supported macros.

```c filename=include/macros.h
#ifndef MACROS_H
#define MACROS_H
#define ADD(left, right) ((left) + (right))
#define SUM3(first, second, third) ((first) + (second) + (third))
#define APPLY(left, right) ADD(left, right)
#endif
```

```c filename=main.c
#include "include/macros.h"

int32 run() {
    return APPLY(2, 3);
}

int32 nested() {
    return ADD((1 + 2), SUM3(1, 2, 3));
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
    ensures result == 9;
} by {
    execute();
    simp();
}
```

```expect
pass
```
