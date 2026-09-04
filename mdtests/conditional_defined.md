# `defined` conditionals follow the active macro set

The bounded preprocessor subset accepts exact `defined(NAME)` and
`!defined(NAME)` tests. They observe literal macro definitions from included
headers and later `#undef` directives, while unrelated branches are removed
before C parsing.

```c filename=include/config.h
#define FEATURE 1
```

```c filename=main.c
#include "include/config.h"

#if defined(FEATURE)
int32 from_header() { return 4; }
#endif

#undef FEATURE
#if !defined(FEATURE)
int32 after_undef() { return 5; }
#endif

#if defined(MISSING)
#include "missing.h"
#endif
```

```click
verifying "main.c";

int32 from_header() {
    ensures result == 4;
} by {
    execute();
    simp();
}

int32 after_undef() {
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
pass
```
