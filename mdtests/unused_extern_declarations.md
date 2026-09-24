# Unused external declarations need no modeled storage

Headers may declare objects supplied by a system library. Their declarations
are checked, but an unrelated verified function does not need definitions for
objects it never names.

```c filename=include/library.h
struct Pair {
    int32 first;
    int32 second;
};

extern int32 status;
extern int32 values[2];
extern struct Pair pair;
extern struct Pair pairs[2];
```

```c filename=unused_extern_declarations.c
#include "include/library.h"

int32 answer() {
    return 42;
}
```

```click
verifying "unused_extern_declarations.c";

int32 answer() {
    ensures result == 42 by auto;
}
```

```expect
pass
```
