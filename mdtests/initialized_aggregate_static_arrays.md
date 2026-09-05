# initialized aggregate arrays link and persist

Fixed-size one-dimensional arrays of supported struct aggregates use one
stable byte-addressed block. Positional element initializers populate the
explicit fields, omitted fields and elements remain zero, an `extern` array
shares its definition across translation units, and file-scope or
function-local `static` arrays retain updates across calls.

```c filename=include/entry.h
#ifndef ENTRY_H
#define ENTRY_H
struct entry {
    int32 value;
    uint8 ready;
};
extern struct entry shared_table[2];
int32 bump_shared();
#endif
```

```c filename=shared.c
#include "include/entry.h"

struct entry shared_table[2] = {{7, 1}, {3}};

int32 bump_shared() {
    shared_table[1].value = shared_table[1].value + 1;
    return shared_table[1].value;
}
```

```c filename=private.c
#include "include/entry.h"

static struct entry private_table[2] = {{4, 1}, {5}};

int32 increment_private() {
    static struct entry local_table[2] = {{2}, {6, 1}};
    private_table[1].value = private_table[1].value + 1;
    local_table[0].value = local_table[0].value + 1;
    return private_table[1].value + local_table[0].value;
}
```

```c filename=runner.c
#include "include/entry.h"
int32 increment_private();

int32 run() {
    bump_shared();
    bump_shared();
    increment_private();
    increment_private();
    return shared_table[1].value;
}
```

```click
verifying "shared.c";
verifying "private.c";
verifying "runner.c";

int32 bump_shared() {
    mutable shared_table[1].value[0..1] by auto;
    ensures result == old(shared_table[1].value) + 1 by auto;
    ensures shared_table[1].value == old(shared_table[1].value) + 1 by auto;
}

int32 increment_private() {
    mutable private_table[1].value[0..1], local_table[0].value[0..1] by auto;
    ensures result == old(private_table[1].value) + old(local_table[0].value) + 2 by auto;
    ensures private_table[1].value == old(private_table[1].value) + 1 by auto;
    ensures local_table[0].value == old(local_table[0].value) + 1 by auto;
}

int32 run() {
    ensures result == 5 by auto;
}
```

```expect
pass
```
