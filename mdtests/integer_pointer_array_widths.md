# Integer-width pointer and array forms

The non-scalar integer types retain their declared element width when used in
local arrays, pointer parameters, and pointer indexing. `size_t` is the
unsigned 64-bit index type on the modeled LP64 ABI.

```c filename=integer_pointer_array_widths.c
#include <stdint.h>

int16_t local_int16_array() {
    int16_t values[2];
    values[0] = 3;
    values[1] = 5;
    return values[1];
}

uint64_t local_uint64_array() {
    uint64_t values[2];
    values[0] = 7ULL;
    values[1] = 11ULL;
    return values[1];
}

uint16_t local_uint16_array() {
    uint16_t values[2];
    values[0] = 13;
    values[1] = 17;
    return values[1];
}

uint32_t local_uint32_array() {
    uint32_t values[2];
    values[0] = 19U;
    values[1] = 23U;
    return values[1];
}

int64_t local_int64_array() {
    int64_t values[2];
    values[0] = -29LL;
    values[1] = 31LL;
    return values[1];
}

int64_t read_int64(size_t index, int64_t values[2]) {
    return values[index];
}

uint16_t read_uint16(size_t index, uint16_t values[2]) {
    return values[index];
}

uint32_t read_uint32(size_t index, uint32_t values[2]) {
    return values[index];
}

int16_t* read_int16_pointer_slot(int16_t* values[2]) {
    return values[1];
}

uint64_t* read_uint64_pointer_slot(uint64_t* values[2]) {
    return values[1];
}
```

```click
verifying "integer_pointer_array_widths.c";

int16_t local_int16_array() {
    ensures result == 5;
}

uint64_t local_uint64_array() {
    ensures result == 11;
}

uint16_t local_uint16_array() {
    ensures result == 17;
}

uint32_t local_uint32_array() {
    ensures result == 23;
}

int64_t local_int64_array() {
    ensures result == 31;
}

int64_t read_int64(size_t index, int64_t values[2]) {
    requires index == 1;
    requires loadable(values[0..2]);
    views values[0..2];
    ensures result == values[1] by auto;
}

uint16_t read_uint16(size_t index, uint16_t values[2]) {
    requires index == 1;
    requires loadable(values[0..2]);
    views values[0..2];
    ensures result == values[1] by auto;
}

uint32_t read_uint32(size_t index, uint32_t values[2]) {
    requires index == 1;
    requires loadable(values[0..2]);
    views values[0..2];
    ensures result == values[1] by auto;
}

int16_t* read_int16_pointer_slot(int16_t* values[2]) {
    requires loadable(values[0..2]);
    views values[0..2];
    ensures result == values[1] by auto;
}

uint64_t* read_uint64_pointer_slot(uint64_t* values[2]) {
    requires loadable(values[0..2]);
    views values[0..2];
    ensures result == values[1] by auto;
}
```

```expect
pass
```
