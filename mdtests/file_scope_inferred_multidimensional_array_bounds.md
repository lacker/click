# initialized multidimensional arrays may infer their outer bound

An external-linkage multidimensional definition may omit its outer bound when
it has nested positional initializer groups. The number of rows becomes the
outer dimension, while shorter rows retain the normal zero-fill behavior.

```c filename=include/tables.h
#ifndef TABLES_H
#define TABLES_H
extern int32 table[][3];
#endif
```

```c filename=reader.c
#include "include/tables.h"

int32 read_table() {
    return table[0][2] + table[1][2];
}
```

```c filename=definitions.c
#include "include/tables.h"

int32 table[][3] = {{1, 2}, {4, 5, 6}};

int32 definition_anchor() {
    return table[0][1];
}
```

```click
verifying "reader.c";
verifying "definitions.c";

int32 read_table() {
    requires table[0][2] == 0 and table[1][2] == 6;
    ensures result == 6 by auto;
    ensures table[0][2] == 0 by auto;
    ensures table[1][2] == 6 by auto;
}

int32 definition_anchor() {
    requires table[0][1] == 2;
    ensures result == 2 by auto;
}
```

```expect
pass
```
