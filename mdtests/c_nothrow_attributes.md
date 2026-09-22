# Nothrow annotations preserve ordinary C effects

The annotation can occur on prototypes, ordinary definitions, or inline
helpers. It does not make a store pure or supply ownership of its target.

```c filename=include/helpers.h
extern int set(int *p) __attribute__((__nothrow__));
static inline __attribute__((always_inline, nothrow)) int helper(int *p) {
    *p = 7;
    return *p;
}
```

```c filename=nothrow.c
#include "include/helpers.h"
__attribute__((nothrow)) int set(int *p) {
    return helper(p);
}
int run(void) {
    int value = 0;
    return set(&value);
}
```

```click
verifying "nothrow.c";
int set(int *p) {
    owns p[0..1];
    ensures p[0] == 7 by auto;
    ensures result == 7 by auto;
}
```

```expect
pass
```
