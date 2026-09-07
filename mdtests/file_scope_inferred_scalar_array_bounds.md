# file-scope scalar arrays may infer a positional bound

A file-scope scalar array definition may omit its bound when a non-empty
positional initializer supplies the elements. The same form works for
translation-unit-private `static` storage, while an `extern` declaration in a
header can refer to the inferred external definition.

```c filename=include/tables.h
#ifndef TABLES_H
#define TABLES_H
extern int32 values[];
#endif
```

```c filename=definitions.c
#include "include/tables.h"

int32 values[] = {2, 6, 9};
static uint8 flags[] = {1, 0, 1};

int32 read_flags() {
    return flags[1];
}

int32 definition_anchor() {
    return values[0];
}
```

```c filename=reader.c
#include "include/tables.h"

int32 run() {
    return values[1];
}
```

```click
verifying "definitions.c";
verifying "reader.c";

int32 read_flags() {
    ensures result == 0 by auto;
}

int32 definition_anchor() {
    ensures result == 2 by auto;
}

int32 run() {
    ensures result == 6 by auto;
}
```

```expect
pass
```
