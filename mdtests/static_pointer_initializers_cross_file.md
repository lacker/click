# static-storage pointer initializers preserve cross-file addresses

A pointer with static storage duration may be initialized from the address of
a declared scalar object. The address remains the target's stable global block
when the pointer and target are defined in one translation unit and used from
another, and a function-local static pointer keeps the same behavior.

```c filename=include/pointers.h
#ifndef POINTERS_H
#define POINTERS_H
extern int32 target;
extern const int32 *target_alias;
int32 read_target_alias();
int32 read_static_alias();
#endif
```

```c filename=target.c
#include "include/pointers.h"

int32 target = 3;
const int32 *target_alias = &target;

int32 read_target_alias() {
    return *target_alias;
}

int32 read_static_alias() {
    static const int32 *local_alias = &target;
    return *local_alias;
}
```

```c filename=reader.c
#include "include/pointers.h"

int32 run() {
    int32 external_value;
    int32 static_value;
    external_value = read_target_alias();
    static_value = read_static_alias();
    return external_value + static_value;
}
```

```click
verifying "target.c" as target_file;
verifying "reader.c";

int32 read_target_alias() {
    owns &target_file::target_alias[0..1];
    owns target_file::target_alias[0..1];
    ensures result == target_file::target_alias[0] by auto;
}

int32 read_static_alias() {
    owns &target_file::read_static_alias::local_alias[0..1];
    owns target_file::read_static_alias::local_alias[0..1];
    ensures result == target_file::read_static_alias::local_alias[0] by auto;
}

int32 run() {
    owns &target_file::target_alias[0..1];
    owns target_file::target_alias[0..1];
    owns &target_file::read_static_alias::local_alias[0..1];
    owns target_file::read_static_alias::local_alias[0..1];
    requires target_file::target_alias[0] == 3;
    requires target_file::read_static_alias::local_alias[0] == 3;
    ensures result == 6;
} by {
    have target_file::target_alias[0] == 3 by simp;
    have target_file::read_static_alias::local_alias[0] == 3 by simp;
    execute();
    simp();
}
```

```expect
fail: run.contract
```
