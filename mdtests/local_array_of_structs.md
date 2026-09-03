# Local arrays of structs use ABI-sized element strides

Indexed struct values lower their field accesses through the existing typed
struct-pointer model. The local array block uses the complete LP64 struct size,
including padding, when computing each element address.

```c filename=local_array_of_structs.c
struct item {
    uint8 tag;
    int32 value;
};

int32 local_array_of_structs() {
    struct item items[2];
    items[0].tag = 3;
    items[1].value = 7;
    return items[0].tag + items[1].value;
}
```

```click
verifying "local_array_of_structs.c";

int32 local_array_of_structs() {
    ensures result == 10 by auto;
}
```

```expect
pass
```
