# owned allocation authorizes a direct free effect

Deallocation is a heap-lifetime transition, not an ordinary write to the
function's mutable byte footprint. A function may directly free a symbolic,
runtime-sized allocation that it owns while mutating an unrelated surviving
object.

```c filename=heap_free_owned_allocation_effect.c
int32 heap_free_owned_allocation_effect(int32 data[], int32 count, int32 flag[]) {
    flag[0] = 9;
    free(data);
    return flag[0];
}
```

```click
resource allocated_int32s(data: int32*, count: int32) {
    contains allocation(data, count * 4);
    owns data[0..count];
    fact data != 0;
}

verifying "heap_free_owned_allocation_effect.c";

int32 heap_free_owned_allocation_effect(int32 data[], int32 count, int32 flag[]) {
    requires 1 <= count;
    requires count <= 536870911;
    consumes allocated_int32s(data, count);
    owns flag[0..1];
    mutable flag[0..1];
    ensures result == 9;
} by {
    unfold(allocated_int32s(data, count));
    execute();
    frame();
    simp();
}
```

```expect
pass
```
