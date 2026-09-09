# designated scalar static arrays link and zero-fill

Static scalar arrays may use literal array-index designators. The selected
elements are initialized in source order, omitted elements retain zero, and
the same behavior applies to external globals, file-scope `static` arrays,
and function-local `static` arrays.

```c filename=include/tables.h
extern int32 shared_table[5];
int32 read_shared();
int32 read_private();
```

```c filename=shared.c
#include "include/tables.h"

int32 shared_table[5] = {
    [4] = 9,
    [1] = 3,
    6
};

int32 read_shared() {
    return shared_table[0] + shared_table[1]
        + shared_table[2] + shared_table[3] + shared_table[4];
}
```

```c filename=private.c
#include "include/tables.h"

static int32 private_table[4] = {
    [2] = 5
};

int32 read_private() {
    static int32 local_table[4] = {
        [3] = 4,
        [1] = 2
    };
    return private_table[0] + private_table[2]
        + local_table[0] + local_table[1]
        + local_table[2] + local_table[3];
}

int32 run() {
    int32 shared;
    int32 private;
    shared = read_shared();
    private = read_private();
    return shared + private;
}
```

```click
verifying "shared.c";
verifying "private.c" as private_file;

int32 read_shared() {
    requires shared_table[0] == 0;
    requires shared_table[1] == 3;
    requires shared_table[2] == 6;
    requires shared_table[3] == 0;
    requires shared_table[4] == 9;
    ensures result == 18 by auto;
}

int32 read_private() {
    owns private_table[0..4];
    owns local_table[0..4];
    requires private_table[0] > -1000;
    requires private_table[0] < 1000;
    requires private_table[2] > -1000;
    requires private_table[2] < 1000;
    requires local_table[0] > -1000;
    requires local_table[0] < 1000;
    requires local_table[1] > -1000;
    requires local_table[1] < 1000;
    requires local_table[2] > -1000;
    requires local_table[2] < 1000;
    requires local_table[3] > -1000;
    requires local_table[3] < 1000;
    ensures result == private_table[0] + private_table[2] + local_table[0] + local_table[1] + local_table[2] + local_table[3] by auto;
}

int32 run() {
    owns private_file::private_table[0..4];
    owns private_file::read_private::local_table[0..4];
    requires shared_table[0] == 0;
    requires shared_table[1] == 3;
    requires shared_table[2] == 6;
    requires shared_table[3] == 0;
    requires shared_table[4] == 9;
    requires private_file::private_table[0] == 0;
    requires private_file::private_table[1] == 0;
    requires private_file::private_table[2] == 5;
    requires private_file::private_table[3] == 0;
    requires private_file::read_private::local_table[0] == 0;
    requires private_file::read_private::local_table[1] == 2;
    requires private_file::read_private::local_table[2] == 0;
    requires private_file::read_private::local_table[3] == 4;
    requires private_file::private_table[0] > -1000;
    requires private_file::private_table[0] < 1000;
    requires private_file::private_table[2] > -1000;
    requires private_file::private_table[2] < 1000;
    requires private_file::read_private::local_table[0] > -1000;
    requires private_file::read_private::local_table[0] < 1000;
    requires private_file::read_private::local_table[1] > -1000;
    requires private_file::read_private::local_table[1] < 1000;
    requires private_file::read_private::local_table[2] > -1000;
    requires private_file::read_private::local_table[2] < 1000;
    requires private_file::read_private::local_table[3] > -1000;
    requires private_file::read_private::local_table[3] < 1000;
    ensures result == 29;
} by {
    have shared_table[0] == 0 by simp;
    have shared_table[1] == 3 by simp;
    have shared_table[2] == 6 by simp;
    have shared_table[3] == 0 by simp;
    have shared_table[4] == 9 by simp;
    step();
    have private_file::private_table[0] == 0 by simp;
    have private_file::private_table[2] == 5 by simp;
    have private_file::read_private::local_table[0] == 0 by simp;
    have private_file::read_private::local_table[1] == 2 by simp;
    have private_file::read_private::local_table[2] == 0 by simp;
    have private_file::read_private::local_table[3] == 4 by simp;
    have private_file::private_table[0] > -1000 by simp;
    have private_file::private_table[0] < 1000 by simp;
    have private_file::private_table[2] > -1000 by simp;
    have private_file::private_table[2] < 1000 by simp;
    have private_file::read_private::local_table[0] > -1000 by simp;
    have private_file::read_private::local_table[0] < 1000 by simp;
    have private_file::read_private::local_table[1] > -1000 by simp;
    have private_file::read_private::local_table[1] < 1000 by simp;
    have private_file::read_private::local_table[2] > -1000 by simp;
    have private_file::read_private::local_table[2] < 1000 by simp;
    have private_file::read_private::local_table[3] > -1000 by simp;
    have private_file::read_private::local_table[3] < 1000 by simp;
    step();
    step();
    step();
    step();
    step();
    simp();
}
```

```expect
fail: run.contract
```
