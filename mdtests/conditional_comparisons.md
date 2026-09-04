# Bounded comparison conditionals select configured branches

The bounded preprocessor subset supports `==` and `!=` between integer or
character literals, literal-valued macros, and `defined(NAME)`. Comparisons
can be combined with the existing boolean operators.

```c filename=include/config.h
#ifndef CONFIG_H
#define CONFIG_H
#define VALUE 4
#endif
```

```c filename=main.c
#include "include/config.h"

#define FEATURE 1
#define DISABLED 0
#define VERSION 0x02
#define NUL '\0'

#if FEATURE == 1
int32 feature_path() { return VALUE; }
#else
#include "missing.h"
#endif

#if DISABLED != 1
int32 disabled_path() { return 5; }
#endif

#if DISABLED == 1
int32 wrong_elif_path() { return 0; }
#elif FEATURE != 0
int32 elif_path() { return 8; }
#else
int32 wrong_elif_else_path() { return 0; }
#endif

#if VERSION == 2 && NUL == 0 && defined(FEATURE) != 0
int32 combined_path() { return 6; }
#endif

#if FEATURE == 0 || VERSION != 2
int32 wrong_path() { return 0; }
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

int32 disabled_path() {
    ensures result == 5;
} by {
    execute();
    simp();
}

int32 elif_path() {
    ensures result == 8;
} by {
    execute();
    simp();
}

int32 combined_path() {
    ensures result == 6;
} by {
    execute();
    simp();
}
```

```expect
pass
```
