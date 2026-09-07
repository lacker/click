# incomplete tentative multidimensional arrays resolve at bundle link time

An external-linkage multidimensional array definition may omit its outer
bound when another translation unit supplies the complete fixed-size
definition. The tentative declaration retains its inner shape for indexing,
and the linked array uses the complete definition's storage and values.

```c filename=include/tables.h
#ifndef TABLES_H
#define TABLES_H
extern int32 table[][3];
#endif
```

```c filename=reader.c
#include "include/tables.h"

int32 table[][3];

int32 read_incomplete() {
    return table[1][2];
}

int32 run() {
    return read_incomplete();
}
```

```c filename=definitions.c
#include "include/tables.h"

int32 table[2][3] = {{2, 6, 9}, {4, 7, 11}};

int32 definition_anchor() {
    return table[0][0];
}
```

```click
verifying "reader.c";
verifying "definitions.c";

int32 read_incomplete() {
    ensures result == 11 by auto;
}

int32 run() {
    ensures result == 11 by auto;
}

int32 definition_anchor() {
    ensures result == 2 by auto;
}
```

```expect
pass
```
