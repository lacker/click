# Iterated ownership refuses to fold while a taken element's guard is true

At every fold the iterated fact must hold exactly the elements whose guard
is true. Here the element at `index` was taken out and its guard
`occupied[index] == 0` is still true, so the fact has a hole where its
definition says it holds a cell, and folding `arena_cells` is refused. The
accepted form marks the cell occupied before folding, as in
[`iterated_ownership_allocate_one.md`](iterated_ownership_allocate_one.md).

```c filename=iterated_ownership_rejects_fold_with_element_out.c
void poke(int32* data, int32* occupied, int32 capacity, int32 index) {
    if (occupied[index] != 0) {
        return;
    }
    data[index] = 7;
}
```

```click
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "iterated_ownership_rejects_fold_with_element_out.c";

void poke(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= index;
    requires index < capacity;
} by {
    unfold(arena_cells(data, occupied, capacity));
    if occupied[index] != 0 {
        execute();
        fold(arena_cells(data, occupied, capacity));
        simp();
    } else {
        take(data[index..index + 1]);
        execute();
        fold(arena_cells(data, occupied, capacity));
        simp();
    }
}
```

```expect
fail: has index `index` taken out
```
