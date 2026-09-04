# Embedded struct arrays copied by value

One-dimensional arrays of embedded structs are part of the recursive
by-value aggregate model. The array elements retain their complete ABI stride
and are copied as typed leaf fields, so updating a nested element in the copy
does not mutate the caller's original element.

```c filename=struct_by_value_embedded_array_finish.c
struct point {
    int32 value;
    uint8 flag;
};

struct packet {
    uint8 tag;
    struct point points[2];
    int32 tail;
};

struct packet finish(struct packet value) {
    struct packet local;
    local = value;
    local.points[1].value = 7;
    local.points[1].flag = 9;
    local.tail = 6;
    return local;
}
```

```c filename=struct_by_value_embedded_array_run.c
struct point {
    int32 value;
    uint8 flag;
};

struct packet {
    uint8 tag;
    struct point points[2];
    int32 tail;
};

int32 run_struct_by_value_embedded_array() {
    struct packet original;
    struct packet copy;
    original.tag = 8;
    original.points[1].value = 4;
    original.points[1].flag = 2;
    original.tail = 5;
    copy = finish(original);
    return original.points[1].value * 100 + copy.points[1].value * 10
        + copy.points[1].flag + original.tag + copy.tail;
}
```

```click
verifying "struct_by_value_embedded_array_finish.c";
verifying "struct_by_value_embedded_array_run.c";

struct packet finish(struct packet value) {
    ensures result.points[1].value == 7;
    ensures result.points[1].flag == 9;
    ensures result.tail == 6;
} by {
    auto;
}

int32 run_struct_by_value_embedded_array() {
    ensures result == 493;
} by {
    execute();
    simp();
}
```

```expect
pass
```
