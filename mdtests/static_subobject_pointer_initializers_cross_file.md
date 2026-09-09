# static pointer initializers can name array elements and struct fields

Static-storage pointers may use the address of a scalar array element or a
scalar struct field. The target is resolved to the containing global block
plus its ABI byte offset, and the same address remains visible across
translation units.

```c filename=include/storage.h
#ifndef STORAGE_H
#define STORAGE_H
extern int32 table[3];
struct state {
    int32 timeout;
    uint8 bytes[4];
};
extern struct state shared;
extern int32 *middle;
extern int32 *timeout_pointer;
extern uint8 *byte_pointer;
int32 read_subobjects();
#endif
```

```c filename=storage.c
#include "include/storage.h"

int32 table[3] = {4, 6, 8};
struct state shared;
int32 *middle = &table[1];
int32 *timeout_pointer = &shared.timeout;
uint8 *byte_pointer = &shared.bytes[2];

int32 read_subobjects() {
    return *middle + *timeout_pointer + *byte_pointer;
}
```

```c filename=reader.c
#include "include/storage.h"

int32 run() {
    return read_subobjects();
}
```

```click
verifying "storage.c" as storage_file;
verifying "reader.c";

int32 read_subobjects() {
    owns storage_file::middle[0..1];
    owns storage_file::timeout_pointer[0..1];
    owns storage_file::byte_pointer[0..1];
    requires storage_file::middle[0] == 6 and storage_file::timeout_pointer[0] == 0 and storage_file::byte_pointer[0] == 0;
    ensures result == 6 by auto;
}

int32 run() {
    owns storage_file::middle[0..1];
    owns storage_file::timeout_pointer[0..1];
    owns storage_file::byte_pointer[0..1];
    requires storage_file::middle[0] == 6 and storage_file::timeout_pointer[0] == 0 and storage_file::byte_pointer[0] == 0;
    ensures result == 6;
} by {
    have storage_file::middle[0] == 6 by simp;
    have storage_file::timeout_pointer[0] == 0 by simp;
    have storage_file::byte_pointer[0] == 0 by simp;
    step();
    step();
    simp();
}
```

```expect
pass
```
