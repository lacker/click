# aggregate globals and function-local statics keep typed field state

Zero-initialized struct objects may be shared through an external declaration
or kept private to the function that owns a `static` declaration. Contracts
authorize the individual scalar fields that the function writes.

```c filename=include/state.h
#ifndef STATE_H
#define STATE_H
struct state {
    int32 value;
    uint8 ready;
};
extern struct state shared;
int32 bump_shared();
#endif
```

```c filename=shared.c
#include "include/state.h"

struct state shared;

int32 bump_shared() {
    shared.value = shared.value + 1;
    shared.ready = 1;
    return shared.value;
}
```

```c filename=private.c
#include "include/state.h"

static struct state file_private;

int32 increment_private() {
    static struct state private;
    private.value = private.value + 1;
    return private.value;
}

int32 increment_file_private() {
    file_private.value = file_private.value + 1;
    return file_private.value;
}
```

```c filename=runner.c
#include "include/state.h"
int32 increment_private();
int32 increment_file_private();

int32 run() {
    int32 first;
    int32 second;
    int32 private_value;
    int32 file_private_value;
    first = bump_shared();
    second = bump_shared();
    private_value = increment_private();
    file_private_value = increment_file_private();
    return first + second + private_value + file_private_value;
}
```

```click
verifying "shared.c";
verifying "private.c";
verifying "runner.c";

int32 bump_shared() {
    mutable shared.value[0..1], shared.ready[0..1] by auto;
    ensures result == old(shared.value) + 1 by auto;
    ensures shared.value == old(shared.value) + 1 by auto;
    ensures shared.ready == 1 by auto;
}

int32 increment_private() {
    mutable private.value[0..1] by auto;
    ensures result == old(private.value) + 1 by auto;
    ensures private.value == old(private.value) + 1 by auto;
}

int32 increment_file_private() {
    mutable file_private.value[0..1] by auto;
    ensures result == old(file_private.value) + 1 by auto;
    ensures file_private.value == old(file_private.value) + 1 by auto;
}

int32 run() {
    ensures result == 5 by auto;
}
```

```expect
pass
```
