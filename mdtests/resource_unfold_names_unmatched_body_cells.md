# Unfolding an unmatched field-bearing body names its cells

A resource with fields and no `match` has one body shape, so `unfold`
exposes that body exactly as it exposes a matched instance's selected arm.
The cells the body owns, here `b->p` and `b->n`, are named in the state at
their folded values, so a later C read of `b->p` is the same load the body's
range was written over.

Before that naming, only a matched arm's cells were named. A loop that writes
through `b->p[from..to]` then havocs its footprint, the unnamed `b->p` read at
the loop head became a fresh load, and the loop's declared range no longer
matched the range the unfold had exposed: the loop was refused with "loop
declares a resource the enclosing function does not hold". A read-only loop
has no footprint and was unaffected.

```c filename=resource_unfold_names_unmatched_body_cells.c
struct buffer {
    int32* p;
    int32 n;
};

void fill(struct buffer* b, int32 from, int32 to) {
    int32 i;
    i = from;
    while (i < to) {
        b->p[i] = 1;
        i = i + 1;
    }
}
```

```click
resource filled_prefix(b: struct buffer*) {
    field prefix: int32;
    owns &b->p;
    owns b->n;
    owns b->p[0..b->n];
    fact 0 <= prefix;
    fact prefix <= b->n;
    fact separate(memory(object(b)), memory(b->p[0..b->n]));
}

verifying "resource_unfold_names_unmatched_body_cells.c";

void fill(struct buffer* b, int32 from, int32 to) {
    owns r: filled_prefix(b);
    requires 0 <= from;
    requires from <= to;
    requires to <= r.prefix;
    ensures r.prefix == old(r.prefix);
} by {
    let { prefix: q } = unfold(r);
    have to <= b->n by {
        apply(int32_le_transitive(to, q, b->n)) using { to <= q; q <= b->n; }
    }
    step();
    step();
    loop {
        decreases to - i;
        invariant from <= i and i <= to;
        owns b->p[from..to];
    }
    execute();
    let r = fold(filled_prefix(b), { prefix: q });
    simp();
}
```

```expect
pass
```
