# Bounded conditional compilation selects active source branches

Click supports `#if 0`, `#if 1`, `#if NAME` for a known 0/1 macro, `#ifdef`,
`#ifndef`, `#else`, and `#endif`. Inactive branches are removed before the C0
parser sees the translation unit, so unsupported code and missing includes in
those branches do not affect verification.

```c filename=include/config.h
#ifndef CONFIG_H
#define CONFIG_H
#define FEATURE 1
#define VALUE 4
#endif
```

```c filename=worker.c
#include "include/config.h"

#if FEATURE
int32 add_config(int32 value) {
    return value + VALUE;
}
#else
#include "missing.h"
#endif
```

```c filename=main.c
#include "include/config.h"

int32 add_config(int32 value);

#if FEATURE
int32 run(int32 value) {
    return add_config(value);
}
#else
int32 run(int32 value) {
    return 0;
}
#endif
```

```click
verifying "worker.c";
verifying "main.c";

int32 add_config(int32 value) {
    requires value <= 2147483643;
    ensures result == value + 4;
}

int32 run(int32 value) {
    requires value <= 2147483643;
    ensures result == value + 4;
} by {
    execute();
    simp();
}
```

```expect
pass
```
