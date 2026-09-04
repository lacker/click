# Bounded `#elif` chains select the first true branch

Each `#elif` uses the same bounded condition forms as `#if`. Once a branch is
selected, later conditions are skipped, so an unsupported expression in a
dead branch does not change the translation unit.

```c filename=include/config.h
#define FEATURE 0
```

```c filename=main.c
#include "include/config.h"

#if FEATURE
int32 wrong_feature(void) { return 0; }
#elif 0
int32 wrong_literal(void) { return 0; }
#elif 1
int32 run() { return 7; }
#elif defined(SKIPPED)
#include "missing.h"
#else
int32 wrong_else(void) { return 0; }
#endif
```

```click
verifying "main.c";

int32 run() {
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
