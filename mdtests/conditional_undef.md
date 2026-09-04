# `#undef` updates macro state across included files

Literal object-like macros can be removed and later redefined. The change is
visible to both conditional compilation and macro expansion in the rest of the
translation unit.

```c filename=include/config.h
#ifndef CONFIG_H
#define CONFIG_H
#define FEATURE 1
#define VALUE 4
#endif
```

```c filename=main.c
#include "include/config.h"

#if FEATURE
int32 run() { return VALUE; }
#endif

#undef FEATURE
#ifdef FEATURE
int32 wrong_after_undef() { return 0; }
#else
int32 after_undef() { return 7; }
#endif

#define FEATURE 0
#if FEATURE
int32 wrong_after_redefine() { return 0; }
#else
int32 after_redefine() { return 8; }
#endif
```

```click
verifying "main.c";

int32 run() {
    ensures result == 4;
} by {
    execute();
    simp();
}

int32 after_undef() {
    ensures result == 7;
} by {
    execute();
    simp();
}

int32 after_redefine() {
    ensures result == 8;
} by {
    execute();
    simp();
}
```

```expect
pass
```
