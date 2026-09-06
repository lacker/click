# const aggregate objects across translation units

This verifies that const-qualified struct globals and function-local static
struct arrays retain their read-only status while their fields remain readable
through the normal aggregate-address representation.

```c filename=state.h
#ifndef STATE_H
#define STATE_H
struct state {
    int32 value;
    uint8 ready;
};
extern const struct state shared[2];
int32 read_shared();
#endif
```

```c filename=state.c
#include "state.h"

const struct state shared[2] = {{7, 1}, {3}};

int32 read_shared() {
    static const struct state local[2] = {{2}, {4, 1}};
    return shared[0].value + shared[1].value
        + local[1].value + local[1].ready;
}
```

```c filename=reader.c
#include "state.h"

int32 run() {
    return read_shared();
}
```

```click
verifying "state.c";
verifying "reader.c";

int32 read_shared() {
    ensures result == 15 by auto;
}

int32 run() {
    ensures result == 15 by auto;
}
```

```expect
pass
```
