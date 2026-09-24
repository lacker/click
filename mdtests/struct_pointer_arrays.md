# Fixed pointer arrays in structs

Pointer slots keep their element type and eight-byte stride. A struct copy
preserves the pointer values; an incomplete struct may be named as a pointee
without making its object layout available.

```c filename=pointer_arrays.c
struct opaque;
struct slots { int *values[2]; struct opaque *hidden[2]; int tail; };
int *global_values[2];

int round_trip(int *value) {
    struct slots first;
    first.values[0] = value;
    first.values[1] = 0;
    first.hidden[0] = 0;
    first.hidden[1] = 0;
    first.tail = 7;
    struct slots copy = first;
    return copy.values[0] == value && copy.values[1] == 0 && copy.tail == 7;
}
int brace_copy(int *value) {
    struct slots first = {{value, 0}, {0, 0}, 5};
    struct slots copy = first;
    return copy.values[0] == value && copy.values[1] == 0 && copy.tail == 5;
}
int local_array(int *value) {
    int *items[2] = {value, 0};
    return items[0] == value && items[1] == 0;
}
int global_round_trip(int *value) {
    global_values[0] = value;
    return global_values[0] == value;
}
int static_round_trip(int *value) {
    static int *saved[2];
    saved[0] = value;
    return saved[0] == value;
}
```

```click
verifying "pointer_arrays.c";
int round_trip(int *value) {
    ensures result == 1;
} by {
    execute();
    simp();
}
int brace_copy(int *value) {
    ensures result == 1;
} by {
    execute();
    simp();
}
int local_array(int *value) {
    ensures result == 1;
} by {
    execute();
    simp();
}
int global_round_trip(int *value) {
    owns global_values[0..2];
    ensures result == 1;
} by {
    execute();
    simp();
}
int static_round_trip(int *value) {
    owns saved[0..2];
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
