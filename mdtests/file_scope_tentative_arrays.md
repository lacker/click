# tentative scalar arrays coalesce across translation units

Fixed-size external scalar arrays follow the same tentative-definition rule as
scalar objects. Repeated compatible declarations without initializers provide
one zero-filled array, while one initialized definition supplies its elements.

```c filename=include/tables.h
#ifndef TABLES_H
#define TABLES_H
extern int32 zero_table[3];
extern int32 initialized_table[3];
int32 bump_tables();
#endif
```

```c filename=tentative.c
#include "include/tables.h"

int32 zero_table[3];
int32 initialized_table[3];

int32 bump_tables() {
    zero_table[1] = zero_table[1] + 1;
    initialized_table[1] = initialized_table[1] + 1;
    return initialized_table[1];
}
```

```c filename=reader.c
#include "include/tables.h"

int32 zero_table[3];
int32 initialized_table[3] = {4, 5};

int32 read_tables() {
    return zero_table[0] + initialized_table[1];
}

int32 run() {
    return bump_tables();
}
```

```click
verifying "tentative.c";
verifying "reader.c";

int32 bump_tables() {
    requires zero_table[1] < 1000 and initialized_table[1] < 1000;
    mutable zero_table[0..3], initialized_table[0..3] by auto;
    ensures result == old(initialized_table[1]) + 1 by auto;
    ensures zero_table[1] == old(zero_table[1]) + 1 by auto;
    ensures initialized_table[1] == old(initialized_table[1]) + 1 by auto;
}

int32 read_tables() {
    requires zero_table[0] == 0 and initialized_table[1] == 5;
    ensures result == 5 by auto;
}

int32 run() {
    owns zero_table[0..3];
    owns initialized_table[0..3];
    requires zero_table[0] == 0 and zero_table[1] < 1000 and initialized_table[1] == 5 and initialized_table[1] < 1000;
    mutable zero_table[0..3], initialized_table[0..3] by auto;
    ensures result == old(initialized_table[1]) + 1 by auto;
}
```

```expect
pass
```
