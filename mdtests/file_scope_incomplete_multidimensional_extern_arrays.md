# incomplete outer dimensions resolve to fixed multidimensional arrays

An external declaration may omit only its outermost bound while retaining
complete inner bounds. The bundle definition supplies the outer bound and
storage, while source indexing uses the retained row-major inner stride.

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
#include "include/tables.h"

int32 table[2][3] = {{1, 2}, {4, 5, 6}};

int32 definition_anchor() {
    return table[0][0];
}
```

```click
verifying "reader.c";
verifying "definitions.c";

int32 read_table() {
    requires table[1][2] == 6;
    ensures result == 6 by auto;
    ensures table[1][2] == 6 by auto;
}

int32 definition_anchor() {
    requires table[0][0] == 1;
    ensures result == 1 by auto;
}
```

```expect
pass
```
