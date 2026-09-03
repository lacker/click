# Inline arrays in struct values

Fixed scalar-array fields retain their inline shape when a struct is passed and
returned by value. Copying visits each element, so the callee can update an
array element without changing the caller's object.

```c filename=struct_by_value_array_finish.c
struct packet {
    uint8 tag;
    int32 values[2];
    uint8 bytes[3];
};

struct packet finish(struct packet value) {
    value.values[0] = 5;
    value.values[1] = value.values[0] + 1;
    value.bytes[0] = 9;
    return value;
}
```

```c filename=struct_by_value_array_run.c
struct packet {
    uint8 tag;
    int32 values[2];
    uint8 bytes[3];
};

int32 run_struct_by_value_array() {
    struct packet original;
    struct packet copy;
    original.tag = 8;
    original.values[0] = 4;
    original.values[1] = 6;
    original.bytes[0] = 8;
    original.bytes[1] = 0;
    original.bytes[2] = 0;
    copy = finish(original);
    return original.values[0] * 100 + copy.values[0] * 10 + copy.values[1]
        + copy.bytes[0] + original.tag;
}
```

```click
verifying "struct_by_value_array_finish.c";
verifying "struct_by_value_array_run.c";

struct packet finish(struct packet value) {
    ensures result.values[0] == 5;
    ensures result.values[1] == 6;
    ensures result.bytes[0] == 9;
} by {
    auto;
}

int32 run_struct_by_value_array() {
    ensures result == 473;
} by {
    execute();
    simp();
}
```

```expect
pass
```
