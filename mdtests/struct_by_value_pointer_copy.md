# Pointer fields copied shallowly in struct values

Data-pointer fields in a by-value struct copy duplicate the pointer value, not
the pointed-to allocation. Updating an ordinary field is isolated in the
callee's copy, while writing through the copied pointer still reaches the
caller's pointee.

```c filename=struct_by_value_pointer_finish.c
struct packet {
    int32* data;
    int32 length;
};

struct packet finish(struct packet value) {
    value.length = 7;
    return value;
}
```

```c filename=struct_by_value_pointer_run.c
struct packet {
    int32* data;
    int32 length;
};

int32 run_struct_by_value_pointer() {
    int32 data[1];
    struct packet original;
    struct packet copy;
    data[0] = 2;
    original.data = data;
    original.length = 4;
    copy = original;
    copy.length = 7;
    copy.data[0] = copy.length;
    return original.length * 100 + copy.length * 10 + data[0];
}
```

```click
verifying "struct_by_value_pointer_finish.c";
verifying "struct_by_value_pointer_run.c";

struct packet finish(struct packet value) {
    ensures result.length == 7;
    ensures result.data == value.data;
} by {
    auto;
}

int32 run_struct_by_value_pointer() {
    ensures result == 477;
} by {
    execute();
    simp();
}
```

```expect
pass
```
