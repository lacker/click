# a postcondition may not read an argument array the function freed

`data` is an external allocation whose block outlives `free` in the memory
model, so the entry-state view of `data[0..count]` must not transport
loadability of `data[0]` into the final snapshot.

```c filename=c_free_rejects_stale_argument_load.c
int32 free_then_read(int32 data[], int32 count) {
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

verifying "c_free_rejects_stale_argument_load.c";

int32 free_then_read(int32 data[], int32 count) {
    requires 1 <= count;
    requires count <= 536870911;
    consumes allocated_int32s(data, count);
    ensures stale: data[0] == data[0];
} by {
    unfold(allocated_int32s(data, count));
    execute();
    simp();
}
```

```expect
fail: loadable
```
