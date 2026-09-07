# Multidimensional global array shapes must agree across files

Two externally linked declarations with the same flattened element count but
different dimensions are different C types and must not share storage.

```c filename=include/tables.h
#ifndef TABLES_H
#define TABLES_H
extern int32 values[2][3];
#endif
```

```c filename=reader.c
#include "include/tables.h"

int32 read_values() {
    return values[1][2];
}
```

```c filename=definitions.c
int32 values[3][2] = {{1, 2}, {3, 4}, {5, 6}};

int32 definition_anchor() {
    return values[0][0];
}
```

```click
verifying "reader.c";
verifying "definitions.c";

int32 read_values() {
    ensures result == 6 by auto;
}

int32 definition_anchor() {
    ensures result == 1 by auto;
}
```

```expect
fail: conflicting declarations for global array `values`
```
