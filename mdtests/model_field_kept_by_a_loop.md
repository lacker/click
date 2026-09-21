# a loop invariant that carries a model field through

The positive side of
[`model_field_across_a_loop_without_an_invariant.md`](model_field_across_a_loop_without_an_invariant.md):
the invariant that refusal prints.

```c filename=model_field_kept_by_a_loop.c
void spin(int32* p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}
```

```click
verifying "model_field_kept_by_a_loop.c";

resource cell(p: int32*) {
    field rank: int32;
    owns p[0..1];
}

void spin(int32* p, int32 n) {
    requires n >= 0;
    owns c: cell(p);
    requires c.rank == 3;
    ensures c.rank == 3;
} by {
    step();
    step();
    loop {
        owns c: cell(p);
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        invariant c.rank == old(c.rank);

        initialize by simp;
        preserve by {
            have 0 <= n - i - 1 by { arithmetic() using { i < n; i >= 0; n >= 0; } }
            have n - i - 1 < n - i by { arithmetic() using { i < n; i >= 0; n >= 0; } }
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
