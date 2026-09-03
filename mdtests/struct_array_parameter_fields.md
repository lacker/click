# Struct array parameters retain their ABI stride

An array parameter of a supported struct type decays to a pointer in C, but
indexed field access still advances by the complete struct size, including
padding.

```c filename=struct_array_parameter_fields.c
struct item {
    uint8 tag;
    int32 value;
};

int32 struct_array_parameter_fields(struct item items[2]) {
    items[1].value = 7;
    return items[0].tag + items[1].value;
}
```

```click
verifying "struct_array_parameter_fields.c";

int32 struct_array_parameter_fields(struct item items[2]) {
    requires loadable(items[0..2]);
    consumes items[0..2];
    ensures result == old(items[0].tag) + 7;
} by {
    step();
    step();
    simp();
}
```

```expect
pass
```
