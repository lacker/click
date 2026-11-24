# Iterated ownership: forming the fact from a known map, and dissolving it

`init_cells` zeroes the whole occupancy map, so every guard of
`arena_cells` holds. `fold(arena_cells(data, occupied, capacity)[..])` then
forms the iterated fact from the covering range `data[0..capacity]` in one
step: the kernel instantiates the quantified map fact once at an arbitrary
index of the range. Whole-clause `unfold` returns the covering range. The proof
forms the whole clause again, then folds the outer resource.

`init_full` marks every cell occupied instead. Every guard is then false, so
the folded clause holds nothing and consumes nothing, and the caller keeps
`data` outright.

```c filename=iterated_ownership_whole_clause.c
void init_cells(int32* data, int32* occupied, int32 capacity) {
    int32 i;
    i = 0;
    while (i < capacity) {
        occupied[i] = 0;
        i = i + 1;
    }
}

void init_full(int32* data, int32* occupied, int32 capacity) {
    int32 i;
    i = 0;
    while (i < capacity) {
        occupied[i] = 1;
        i = i + 1;
    }
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

verifying "iterated_ownership_whole_clause.c";

void init_cells(int32* data, int32* occupied, int32 capacity) {
    requires 0 <= capacity;
    consumes occupied[0..capacity];
    consumes data[0..capacity];
    produces arena_cells(data, occupied, capacity);
} by {
    step();
    step();
    loop {
        decreases capacity - i;
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 0
        };
        owns occupied[0..capacity];
    }
    have i == capacity;
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 0
    } by {
        rewrite(capacity, i);
        close();
    }
    fold(arena_cells(data, occupied, capacity)[..]);
    mark clause_args;
    unfold(at(clause_args, arena_cells(data, occupied, capacity))[..]);
    fold(arena_cells(data, occupied, capacity)[..]);
    fold(arena_cells(data, occupied, capacity));
}

void init_full(int32* data, int32* occupied, int32 capacity) {
    requires 0 <= capacity;
    consumes occupied[0..capacity];
    produces arena_cells(data, occupied, capacity);
} by {
    step();
    step();
    loop {
        decreases capacity - i;
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 1
        };
        owns occupied[0..capacity];
    }
    have i == capacity;
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 1
    } by {
        rewrite(capacity, i);
        close();
    }
    fold(arena_cells(data, occupied, capacity)[..]);
    fold(arena_cells(data, occupied, capacity));
}
```

```expect
pass
```
