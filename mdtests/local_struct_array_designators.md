# Designated initializers for local arrays of structs

Fixed-dimensional local arrays of copyable structs accept integer array
designators at each array dimension. Positional elements continue after the
most recent designator, and omitted elements are zero-filled.

```c filename=local_struct_array_designators.c
struct inner {
    int32 value;
};

struct item {
    int32 tag;
    struct inner inner;
};

int32 local_struct_array_designators() {
    struct item items[4] = {
        [1] = {.tag = 10, .inner = {.value = 1}},
        {.tag = 20, .inner = {.value = 2}},
        [3] = {.tag = 30, .inner = {.value = 3}}
    };
    return items[1].tag + items[2].tag + items[3].tag
        + items[1].inner.value + items[2].inner.value
        + items[3].inner.value + (items[0].tag == 0);
}

int32 local_struct_matrix_designators() {
    struct item items[2][3] = {
        {
            [1] = {.tag = 1, .inner = {.value = 2}},
            {.tag = 3, .inner = {.value = 4}}
        },
        [1] = {
            [2] = {.tag = 12, .inner = {.value = 3}},
            [0] = {.tag = 10, .inner = {.value = 1}}
        }
    };
    return items[0][1].tag + items[0][2].inner.value
        + items[1][0].tag + items[1][2].tag
        + items[1][2].inner.value
        + (items[0][0].tag == 0) + (items[1][1].tag == 0);
}
```

```click
verifying "local_struct_array_designators.c";

int32 local_struct_array_designators() {
    ensures result == 67 by auto;
}

int32 local_struct_matrix_designators() {
    ensures result == 32 by auto;
}
```

```expect
pass
```
