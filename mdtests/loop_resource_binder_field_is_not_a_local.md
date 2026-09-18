# A loop binder's model field is not the local the loop havocs

At a loop head the kernel invents two unrelated things: an arbitrary value for
every local the body modifies, and an arbitrary model for every resource
instance the loop re-binds. Both are fresh identities from the execution's one
counter, so nothing relates `c.rank` to `i` and `have c.rank == i` has no
proof.

When the two allocators were separate streams that both started at the same
identity, `c.rank` and `i` became the *same* kernel variable and `simp` closed
that `have` outright. With `invariant c.rank == old(c.rank)` and
`requires c.rank == 0` that yields `i == 0` on every visit, and this loop —
which plainly leaves `i == n` — proved the false `ensures n <= 1`.

```c filename=loop_resource_binder_field_is_not_a_local.c
struct cell { int32 value; };

int32 spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_resource_binder_field_is_not_a_local.c";

resource cell(p: struct cell*) {
    field rank: int32;
    owns p->value;
    fact p->value == rank;
}

int32 spin(struct cell* node, int32 n) {
    requires node != 0;
    requires n >= 0;
    owns c: cell(node);
    requires c.rank == 0;
    ensures n <= 1;
} by {
    step();
    step();
    loop {
        owns c: cell(node);
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant i <= 1;
        invariant c.rank == old(c.rank);

        initialize by simp;
        preserve by {
            have c.rank == i by { simp(); }
            have i == 0 by { simp() using { c.rank == i; c.rank == old(c.rank); old(c.rank) == 0; } }
            have 0 <= n - i - 1 by { arithmetic() using { i < n; 0 <= i; } }
            have n - i - 1 < n - i by { arithmetic() using { i < n; 0 <= i; } }
            step();
            close_invariants();
        }
    }
    have n <= 1 by { arithmetic() using { i >= n; i <= 1; } }
    step();
    simp();
}
```

```expect
fail: `have` failed for `c.rank == i`
```
