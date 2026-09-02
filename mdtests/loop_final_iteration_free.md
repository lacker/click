# a loop may release heap storage when its post-body condition is false

```c filename=loop_final_iteration_free.c
int32 loop_final_iteration_free(int32* data) {
    int32 i;
    i = 0;
    while (i < 1) {
        free(data);
        i = i + 1;
    }
    return 0;
}
```

```click
resource allocated_int32s(data: int32*, count: int32) {
    contains allocation(data, count * 4);
    owns data[0..count];
    fact data != 0;
}

verifying "loop_final_iteration_free.c";

int32 loop_final_iteration_free(int32* data) {
    requires data != 0;
    consumes allocated_int32s(data, 1);
    ensures result == 0;
} by {
    unfold(allocated_int32s(data, 1));
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= 1;
        initialize by simp;
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
