# initialized aggregate globals and statics keep their first state

Positional compile-time initializers now populate supported struct globals and
function-local or file-scope `static` objects. Omitted scalar fields retain C's
zero initialization, and an external declaration observes the one initialized
definition across translation units.

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

struct state shared = {7, 1};

int32 bump_shared() {
    shared.value = shared.value + 1;
    return shared.value;
}
```

```c filename=private.c
#include "include/state.h"

static struct state file_private = {4, 1};

int32 increment_local() {
    static struct state local = {3};
    local.value = local.value + 1;
    return local.value;
}

int32 increment_file_private() {
    file_private.value = file_private.value + 1;
    return file_private.value;
}
```

```c filename=runner.c
#include "include/state.h"
int32 increment_local();
int32 increment_file_private();

int32 run() {
    bump_shared();
    bump_shared();
    increment_local();
    increment_local();
    return increment_file_private();
}
```

```click
verifying "shared.c";
verifying "private.c";
verifying "runner.c";

int32 bump_shared() {
    mutable shared.value[0..1] by auto;
    ensures result == old(shared.value) + 1 by auto;
}

int32 increment_local() {
    mutable local.value[0..1] by auto;
    ensures result == old(local.value) + 1 by auto;
    ensures local.ready == 0 by auto;
}

int32 increment_file_private() {
    mutable file_private.value[0..1] by auto;
    ensures result == old(file_private.value) + 1 by auto;
}

int32 run() {
    ensures result == 5 by auto;
}
```

```expect
pass
```
