# pointer arithmetic on a real object is unaffected

The companion to `null_pointer_arithmetic_rejected.md`. Only a pointer in the
null object's block is refused; displacing a pointer that designates storage
still works, comparing a null pointer still decides, and displacing a null
pointer by zero is still accepted, which is the shape real code writes and
which C23 defines.

```c filename=pointer_arithmetic_on_objects.c
int32 offset_into_a_view(int32* values) {
    int32* next = values + 1;
    return next[0];
}

int32 null_compares_equal() {
    int32* start = 0;
    if (start == 0) {
        return 1;
    }
    return 0;
}

int32 null_displaced_by_zero() {
    int32* start = 0;
    int32* same = start + 0;
    if (same == 0) {
        return 1;
    }
    return 0;
}

int32 offset_into_an_allocation() {
    int32* data = malloc(2 * sizeof(int32));
    if (data == 0) {
        return 0;
    }
    data[0] = 1;
    data[1] = 2;
    int32* next = data + 1;
    int32 value = next[0];
    free(data);
    return value;
}
```

```click
verifying "pointer_arithmetic_on_objects.c";

int32 offset_into_a_view(int32* values) {
    views values[0..2];
    ensures result == values[1] by auto;
}

int32 null_compares_equal() {
    ensures result == 1 by auto;
}

int32 null_displaced_by_zero() {
    ensures result == 1 by auto;
}

int32 offset_into_an_allocation() {
    ensures result == 2 or result == 0 by auto;
}
```

```expect
pass
```
