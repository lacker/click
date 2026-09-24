# Iterated guarded ownership: declaration and whole-resource round trip

A resource body may own one element range per index of a bounded range,
held exactly when a guard cell the same body owns says so. The clause is one
resource fact: unfolding the enclosing resource exposes it without
enumerating the range, and folding consumes it back.

Without a guard the clause owns every element, so `plain_cells` is exactly
the range `owns data[0..capacity]` and lowers to it: `touch` writes a cell
of the unfolded body with no `take`.

```c filename=iterated_ownership_declaration.c
void keep(int32* data, int32* occupied, int32 capacity) {}

void touch(int32* data, int32 capacity) {
    data[0] = 1;
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

resource plain_cells(data: int32*, capacity: int32) {
    forall (k: int32) where 0 <= k and k < capacity {
        owns data[k..k + 1];
    }
}

verifying "iterated_ownership_declaration.c";

void keep(int32* data, int32* occupied, int32 capacity) {
    owns arena_cells(data, occupied, capacity);
} by {
    unfold(arena_cells(data, occupied, capacity));
    execute();
    fold(arena_cells(data, occupied, capacity));
    simp();
}

void touch(int32* data, int32 capacity) {
    owns plain_cells(data, capacity);
    requires 0 < capacity;
} by {
    unfold(plain_cells(data, capacity));
    execute();
    fold(plain_cells(data, capacity));
    simp();
}
```

```expect
pass
```
