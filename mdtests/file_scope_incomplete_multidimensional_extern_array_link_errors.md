# incomplete multidimensional array declarations must match inner bounds

The omitted outer bound does not make different inner shapes compatible. A
declaration of `[][3]` cannot link to a definition of `[2][4]`.

```c filename=include/tables.h
#ifndef TABLES_H
#define TABLES_H
extern int32 table[][3];
#endif
```

```c filename=reader.c
#include "include/tables.h"

int32 read_table() {
    return table[1][2];
}
```

```c filename=definitions.c
int32 table[2][4] = {{1, 2}, {3, 4}};

int32 definition_anchor() {
    return table[0][0];
}
```

```click
verifying "reader.c";
verifying "definitions.c";

int32 read_table() {
    ensures result == 2 by auto;
}

int32 definition_anchor() {
    ensures result == 1 by auto;
}
```

```expect
fail: conflicting declarations for global array `table`
```
