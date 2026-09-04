# designated static aggregates link and zero-fill

Static-storage aggregate initializers may designate struct fields with `.field`
and one-dimensional aggregate-array elements with `[literal]`. Designated
fields and elements may appear in any order; omitted fields and elements keep
their static zero value. The same forms work for external globals, file-scope
`static` objects, and function-local `static` objects.

```c filename=include/entry.h
#ifndef ENTRY_H
#define ENTRY_H
struct entry {
    int32 value;
    uint8 ready;
};
extern struct entry shared_table[3];
int32 bump_shared();
#endif
```

```c filename=shared.c
#include "include/entry.h"

struct entry shared_table[3] = {
    [2] = {.ready = 1, .value = 7},
    [1] = {.value = 3},
    [0] = {.ready = 1}
};

int32 bump_shared() {
    shared_table[1].value = shared_table[1].value + 1;
    return shared_table[1].value;
}
```

```c filename=private.c
#include "include/entry.h"

static struct entry private_table[2] = {
    [1] = {.ready = 1, .value = 4}
};

int32 increment_private() {
    static struct entry local = {.value = 2};
    static struct entry local_table[2] = {
        [1] = {.ready = 1, .value = 6}
    };
    private_table[1].value = private_table[1].value + 1;
    local.value = local.value + 1;
    local_table[1].value = local_table[1].value + 1;
    return private_table[1].value + local.value + local_table[1].value;
}
```

```c filename=runner.c
#include "include/entry.h"
int32 increment_private();

int32 run() {
    return shared_table[1].value + shared_table[2].value + shared_table[0].ready;
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
    mutable private_table[1].value[0..1], local.value[0..1], local_table[1].value[0..1] by auto;
    ensures result == old(private_table[1].value) + old(local.value)
        + old(local_table[1].value) + 3 by auto;
    ensures private_table[1].value == old(private_table[1].value) + 1 by auto;
    ensures local.value == old(local.value) + 1 by auto;
    ensures local_table[1].value == old(local_table[1].value) + 1 by auto;
}

int32 run() {
    ensures result == 11 by auto;
}
```

```expect
pass
```
