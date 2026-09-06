# tentative aggregate definitions across translation units

Compatible tentative definitions of supported struct globals and fixed-size
aggregate arrays coalesce into one stable object. A linked initialized
definition supersedes tentative definitions, while a name with only tentative
definitions remains zero-initialized.

```c filename=include/state.h
#ifndef STATE_H
#define STATE_H
struct state {
    int32 value;
    uint8 ready;
};
extern struct state zero;
extern struct state zero_table[2];
extern struct state shared;
extern struct state shared_table[2];
int32 read_initialized();
int32 read_tentative();
#endif
```

```c filename=initialized.c
#include "include/state.h"

struct state zero;
struct state zero_table[2];
struct state shared = {7, 1};
struct state shared_table[2] = {{4, 1}, {3}};

int32 read_initialized() {
    return zero.value + zero_table[0].value + zero_table[1].value
        + shared.value + shared_table[0].value + shared_table[1].value;
}
```

```c filename=tentative.c
#include "include/state.h"

struct state zero;
struct state zero_table[2];
struct state shared;
struct state shared_table[2];

int32 read_tentative() {
    return zero.value + zero_table[0].value + zero_table[1].value
        + shared.value + shared_table[0].value + shared_table[1].value;
}
```

```c filename=runner.c
#include "include/state.h"

int32 run() {
    int32 initialized;
    int32 tentative;
    initialized = read_initialized();
    tentative = read_tentative();
    return initialized + tentative;
}
```

```click
verifying "initialized.c";
verifying "tentative.c";
verifying "runner.c";

int32 read_initialized() {
    ensures result == 14 by auto;
}

int32 read_tentative() {
    ensures result == 14 by auto;
}

int32 run() {
    ensures result == 28 by auto;
}
```

```expect
pass
```
