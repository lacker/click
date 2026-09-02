# loop back edge cannot resurrect a freed heap allocation

```c filename=loop_heap_lifetime_join.c
int32 loop_heap_lifetime_join(int32* data) {
    int32 i;
    i = 0;
    while (i < 1) {
        free(data);
        i = i + 1;
    }
    free(data);
    return 0;
}
```

```click
resource allocated_int32s(data: int32*, count: int32) {
    contains allocation(data, count * 4);
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
        initialize by simp;
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
fail: heap allocation lifetime
```
