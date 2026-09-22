# Leaf annotations retain checked call effects

A leaf function may write through an argument and call another function.
The caller must supply the same ownership that an unannotated call requires.

```c filename=include/leaf.h
extern int set(int *p) __attribute__((__nothrow__, __leaf__));
```

```c filename=leaf.c
#include "include/leaf.h"
__attribute__((leaf)) int set(int *p) {
    *p = 7;
    return *p;
}
```

```c filename=caller.c
#include "include/leaf.h"
__attribute__((__leaf__)) int run(int *p) {
    return set(p);
}
```

```click
verifying "leaf.c";
verifying "caller.c";
int set(int *p) {
    owns p[0..1];
    ensures p[0] == 7 by auto;
    ensures result == 7 by auto;
}
int run(int *p) {
    owns p[0..1];
    ensures p[0] == 7 by auto;
    ensures result == 7 by auto;
}
```

```expect
pass
```
