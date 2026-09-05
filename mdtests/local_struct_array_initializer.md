# Positional initializers for local arrays of structs

Local arrays of copyable structs accept nested positional element groups. Each
element uses the complete ABI-sized struct stride, nested fields are initialized
recursively, and omitted fields or elements become zero.

```c filename=local_struct_array_initializer.c
struct inner {
    int32 value;
    uint8 enabled;
};

struct item {
    uint8 tag;
    struct inner inner;
    int32 values[2];
};

int32 local_struct_array_initializer() {
    struct item items[2] = {
        {1, {10, 1}, {2}},
        {2, {20}, {3, 4}}
    };
    return items[0].tag + items[0].inner.value
        + items[0].inner.enabled + items[0].values[0]
        + items[0].values[1] + items[1].tag
        + items[1].inner.value + items[1].inner.enabled
        + items[1].values[0] + items[1].values[1];
}
```

```click
verifying "local_struct_array_initializer.c";

int32 local_struct_array_initializer() {
    ensures result == 43 by auto;
}
```

```expect
pass
```
