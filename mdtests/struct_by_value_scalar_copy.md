# Scalar-only structs copy by value

The first by-value aggregate slice supports structs whose fields are only
`int32` and `uint8`. Parameters, locals, assignments, and returns use
independent address-backed storage, so a callee update cannot mutate its
caller's original object.

```c filename=struct_by_value_bump.c
struct pair {
    int32 first;
    uint8 tag;
};

struct pair bump(struct pair value) {
    value.first = 5;
    value.tag = 9;
    return value;
}
```

```c filename=struct_by_value_run.c
struct pair {
    int32 first;
    uint8 tag;
};

int32 run_struct_by_value() {
    struct pair original;
    struct pair copy;
    original.first = 4;
    original.tag = 9;
    copy = bump(original);
    return original.first * 100 + copy.first * 10 + copy.tag;
}
```

```click
verifying "struct_by_value_bump.c";
verifying "struct_by_value_run.c";

struct pair bump(struct pair value) {
    ensures result.first == 5;
    ensures result.tag == 9;
} by {
    auto;
}

int32 run_struct_by_value() {
    ensures result == 459;
} by {
    execute();
    simp();
}
```

```expect
pass
```
