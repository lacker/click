# incomplete tentative arrays resolve at bundle link time

An external-linkage array definition may omit its bound when another
translation unit supplies the complete fixed-size definition. The incomplete
definition still provides storage semantics for its own translation unit, and
the linked array keeps the complete definition's element values.

```c filename=include/tables.h
#ifndef TABLES_H
#define TABLES_H
extern int32 values[];
#endif
```

```c filename=reader.c
#include "include/tables.h"

int32 values[];

int32 read_incomplete() {
    return values[1];
}

int32 run() {
    return read_incomplete();
}
```

```c filename=definitions.c
#include "include/tables.h"

int32 values[3] = {2, 6, 9};

int32 definition_anchor() {
    return values[0];
}
```

```click
verifying "reader.c";
verifying "definitions.c";

int32 read_incomplete() {
    requires values[1] == 6;
    ensures result == 6 by auto;
}

int32 run() {
    requires values[1] == 6;
    ensures result == 6 by auto;
}

int32 definition_anchor() {
    requires values[0] == 2;
    ensures result == 2 by auto;
}
```

```expect
pass
```
