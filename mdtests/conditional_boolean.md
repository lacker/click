# Bounded boolean conditionals select configured branches

The bounded preprocessor subset combines its literal, macro, and `defined`
atoms with `!`, `&&`, `||`, and parentheses. It uses normal precedence and
short-circuits branches that are already known to be inactive.

```c filename=include/config.h
#ifndef CONFIG_H
#define CONFIG_H
#define FEATURE 1
#define DISABLED 0
#endif
```

```c filename=main.c
#include "include/config.h"

#if defined(FEATURE) && FEATURE
int32 feature_path() { return 4; }
#else
#include "missing.h"
#endif

#if !defined(MISSING) || DISABLED
int32 fallback_path() { return 5; }
#endif

#if (defined(FEATURE) && !defined(MISSING)) || DISABLED
int32 grouped_path() { return 6; }
#endif

#if 1 || 1 && 0
int32 precedence_path() { return 7; }
#endif

#if 0 && defined(UNKNOWN)
#include "missing_again.h"
#endif
```

```click
verifying "main.c";

int32 feature_path() {
    ensures result == 4;
} by {
    execute();
    simp();
}

int32 fallback_path() {
    ensures result == 5;
} by {
    execute();
    simp();
}

int32 grouped_path() {
    ensures result == 6;
} by {
    execute();
    simp();
}

int32 precedence_path() {
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
