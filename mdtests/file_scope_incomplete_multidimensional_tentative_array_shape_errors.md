# incomplete tentative multidimensional arrays require compatible inner bounds

The complete definition of an incomplete multidimensional tentative array
must preserve every declared inner bound. A different inner shape remains a
link-time declaration conflict.

```c filename=include/tables.h
#ifndef TABLES_H
#define TABLES_H
extern int32 table[][3];
#endif
```

```c filename=reader.c
#include "include/tables.h"

int32 table[][3];

int32 read() {
    return table[1][2];
}
```

```c filename=definitions.c
int32 table[2][4] = {{2, 6, 9, 10}, {4, 7, 11, 12}};

int32 definition_anchor() {
    return table[0][0];
}
```

```click
verifying "reader.c";
verifying "definitions.c";

int32 read() {
    ensures result == 11 by auto;
}

int32 definition_anchor() {
    ensures result == 2 by auto;
}
```

```expect
fail: conflicting declarations for global array `table`
```
