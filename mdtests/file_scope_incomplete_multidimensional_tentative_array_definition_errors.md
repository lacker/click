# incomplete tentative multidimensional arrays still allow only one definition

An incomplete tentative declaration may be completed by one fixed-size
definition, but two initialized definitions of the linked array remain an
error.

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

```c filename=first.c
#include "include/tables.h"

int32 table[2][3] = {{2, 6, 9}, {4, 7, 11}};

int32 first_anchor() {
    return table[0][0];
}
```

```c filename=second.c
#include "include/tables.h"

int32 table[2][3] = {{3, 5, 8}, {13, 21, 34}};

int32 second_anchor() {
    return table[0][0];
}
```

```click
verifying "reader.c";
verifying "first.c";
verifying "second.c";

int32 read() {
    ensures result == 11 by auto;
}

int32 first_anchor() {
    ensures result == 2 by auto;
}

int32 second_anchor() {
    ensures result == 3 by auto;
}
```

```expect
fail: multiple definitions of global array `table`
```
