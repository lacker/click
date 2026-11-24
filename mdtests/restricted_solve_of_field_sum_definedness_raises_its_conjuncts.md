# `close() using` proves a field sum's definedness one conjunct at a time

`defined(pool->checked_out + 1)` lowers to two conjuncts: the read of
`pool->checked_out` is defined, and the sum's Integer bounds hold. Restricted
`solve` splits them and proves each as a goal of its own, so each needs its
Surface form: `defined` names the whole domain, not its parts. The split
raises each child canonically. Without that, the bounds child had no Surface
goal, the search spelled it as `defined(...)` again, and opening that `have`
restated the whole conjunction, which split again until the stack overflowed.
The listed entry bound proves the bounds; `owns *pool` gives the read.

```c filename=pool.c
struct pool { int32 checked_out; int32 capacity; };
void bump(struct pool* pool) { pool->checked_out = pool->checked_out + 1; }
```

```click
verifying "pool.c";
void bump(struct pool* pool) {
    owns *pool;
    requires pool->checked_out < 2147483647;
    ensures pool->checked_out == old(pool->checked_out) + 1;
} by {
    have defined((pool->checked_out + 1)) by {
        close() using { at(function.entry, pool->checked_out) < at(function.entry, 2147483647); };
    }
    step();
    step();
    close();
}
```

```expect
pass
```
