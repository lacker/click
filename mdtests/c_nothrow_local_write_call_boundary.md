# Ordinary calls still require explicit writable resources

The unchanged caller currently cannot lend write ownership of its local scalar
through an ordinary function contract. Nothrow does not supply that ownership;
this regression records the existing call-boundary limitation.

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
int run() {
    ensures result == 7 by auto;
}
```

```expect
fail: missing resource fact `owns local:value
```
