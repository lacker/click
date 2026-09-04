# Nested embedded structs copied by value

By-value structs may contain recursively embedded copyable structs. Parameters,
locals, assignments, and returns use fresh address-backed storage while
preserving the nested ABI offsets, so changing the callee's nested fields does
not mutate the caller's original object.

```c filename=struct_by_value_embedded_finish.c
struct leaf {
    int32 value;
};

struct inner {
    struct leaf leaf;
    uint8 flag;
};

struct outer {
    uint8 tag;
    struct inner inner;
    int32 tail;
};

struct outer finish(struct outer value) {
    value.inner.leaf.value = 5;
    value.inner.flag = 9;
    value.tail = 7;
    return value;
}
```

```c filename=struct_by_value_embedded_run.c
struct leaf {
    int32 value;
};

struct inner {
    struct leaf leaf;
    uint8 flag;
};

struct outer {
    uint8 tag;
    struct inner inner;
    int32 tail;
};

int32 run_struct_by_value_embedded() {
    struct outer original;
    struct outer copy;
    original.tag = 8;
    original.inner.leaf.value = 4;
    original.inner.flag = 2;
    original.tail = 6;
    copy = finish(original);
    return original.inner.leaf.value * 100 + copy.inner.leaf.value * 10
        + copy.inner.flag + original.tag + copy.tail;
}
```

```click
verifying "struct_by_value_embedded_finish.c";
verifying "struct_by_value_embedded_run.c";

struct outer finish(struct outer value) {
    ensures result.inner.leaf.value == 5;
    ensures result.inner.flag == 9;
    ensures result.tail == 7;
} by {
    auto;
}

int32 run_struct_by_value_embedded() {
    ensures result == 474;
} by {
    execute();
    simp();
}
```

```expect
pass
```
