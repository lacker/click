# loop back edge cannot resurrect a freed heap allocation

The body frees `data` on every iteration. The loop head holds the
allocation's authority, and the first `free` consumes it, so the back edge
does not return the ownership the head started with and the second `free`
can never be reached with authority. The refusal is the ownership join: the
ended allocation's tombstone is a diagnostic, and authority is what a back
edge must return.

```c filename=loop_heap_lifetime_join.c
int32 loop_heap_lifetime_join(int32* data) {
    int32 i;
    i = 0;
    while (i < 2) {
        free(data);
        i = i + 1;
    }
    free(data);
    return 0;
}
```

```click
resource allocated_int32s(data: int32*, count: int32) {
    owns allocation(data, count * 4);
    owns data[0..count];
    fact data != 0;
}

verifying "loop_heap_lifetime_join.c";

int32 loop_heap_lifetime_join(int32* data) {
    requires data != 0;
    consumes allocated_int32s(data, 1);
    ensures result == 0;
} by {
    unfold(allocated_int32s(data, 1));
    step();
    step();
    loop {
        invariant 0 <= i;
        initialize by close();
        maintain by {
            step();
            step();
        }
    }
}
```

```expect
fail: loop state join changes resource ownership
```
