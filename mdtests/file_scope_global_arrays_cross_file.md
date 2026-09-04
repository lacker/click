# global scalar arrays link through extern declarations

An `extern` array declaration in a shared header refers to the one definition
in another translation unit. Calls and direct indexed reads observe the same
storage.

```c filename=include/table.h
#ifndef TABLE_H
#define TABLE_H
extern int32 table[3];
int32 increment_middle();
#endif
```

```c filename=table.c
#include "include/table.h"

int32 table[3] = {1, 3, 5};

int32 increment_middle() {
    table[1] = table[1] + 1;
    return table[1];
}
```

```c filename=reader.c
#include "include/table.h"

int32 read_last() {
    return table[2];
}

int32 run() {
    increment_middle();
    return table[1];
}
```

```click
verifying "table.c";
verifying "reader.c";

int32 increment_middle() {
    mutable table[0..3] by auto;
    ensures result == old(table[1]) + 1 by auto;
    ensures table[1] == old(table[1]) + 1 by auto;
}

int32 read_last() {
    ensures result == 5 by auto;
}

int32 run() {
    mutable table[0..3] by auto;
    ensures result == 4 by auto;
}
```

```expect
pass
```
