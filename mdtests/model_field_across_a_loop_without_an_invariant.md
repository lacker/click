# a model field across a loop that states no invariant about it

A loop head is an arbitrary visit, so a binder the loop owns carries whatever
the invariants state about its model — never the model it happened to hold at
loop entry. With no invariant about `rank`, the field after the loop is a fresh
one, and the refusal names the loop and prints the invariant that carries it
through. [`model_field_kept_by_a_loop.md`](model_field_kept_by_a_loop.md) is
that invariant verifying.

```c filename=model_field_across_a_loop_without_an_invariant.c
void spin(int32* p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}
```

```click
verifying "model_field_across_a_loop_without_an_invariant.c";

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
fail: `c.rank` may have changed since function entry: the loop owns `c`, and a loop head is an arbitrary visit, so it gives `c` a fresh model. If the body keeps the field, carry it through as `invariant c.rank == old(c.rank);`.
```
