# Multidimensional file-scope scalar arrays use row-major storage

Fixed-dimensional file-scope scalar arrays retain their C shape for indexed
access while using one stable flat storage block. Nested initializers fill
elements in row-major order, and omitted elements remain zero across
translation units.

```c filename=include/tables.h
#ifndef TABLES_H
#define TABLES_H
extern int32 values[2][3];
extern uint8 flags[2][2];
#endif
```

```c filename=definitions.c
#include "include/tables.h"

int32 values[2][3] = {{1, 2}, {3, 4, 5}};
uint8 flags[2][2];

int32 definition_anchor() {
    return values[0][1];
}
```

```c filename=reader.c
#include "include/tables.h"

int32 read_values() {
    return values[1][2] + flags[0][1];
}

int32 update_values() {
    values[1][0] = values[0][1];
    return values[1][0];
}
```

```click
verifying "definitions.c";
verifying "reader.c";

int32 definition_anchor() {
    requires values[0][1] == 2;
    ensures result == 2 by auto;
}

int32 read_values() {
    owns values[1][2..3];
    owns flags[0][1..2];
    requires values[1][2] > -1000;
    requires values[1][2] < 1000;
    ensures result == values[1][2] + flags[0][1] by auto;
}

int32 update_values() {
    requires values[0][1] == 2;
    mutable values[1][0..1] by auto;
    ensures result == 2 by auto;
    ensures values[1][0] == 2 by auto;
}
```

```expect
pass
```
