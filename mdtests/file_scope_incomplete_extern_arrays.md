# incomplete external arrays resolve at bundle link time

An external array declaration may omit its bound when a different translation
unit supplies the complete fixed-size definition. Scalar and supported struct
arrays retain their normal stable storage and indexed access after linking.

```c filename=include/tables.h
#ifndef TABLES_H
#define TABLES_H
struct state {
    int32 value;
    uint8 ready;
};
extern int32 values[];
extern struct state entries[];
#endif
```

```c filename=reader.c
#include "include/tables.h"

int32 read_incomplete() {
    return values[1] + entries[0].value;
}

int32 run() {
    return read_incomplete();
}
```

```c filename=definitions.c
#include "include/tables.h"

int32 values[3] = {2, 6, 9};
struct state entries[2] = {{4, 1}, {5}};

int32 definition_anchor() {
    return values[0];
}
```

```click
verifying "reader.c";
verifying "definitions.c";

int32 read_incomplete() {
    requires values[1] == 6 and entries[0].value == 4;
    ensures result == 10 by auto;
}

int32 run() {
    requires values[1] == 6 and entries[0].value == 4;
    ensures result == 10 by auto;
}

int32 definition_anchor() {
    requires values[0] == 2;
    ensures result == 2 by auto;
}
```

```expect
pass
```
