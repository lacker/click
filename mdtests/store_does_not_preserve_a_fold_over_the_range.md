# a store does not preserve a fold over the range it writes into

The fold form. `icount` is evaluated at two snapshots, and the fold's own reads
come from the snapshot its array argument names. Nothing relates the two counts,
so the equation is not available; the frame lemma that would relate them needs a
per-cell premise the store does not give.

```c filename=store_does_not_preserve_a_fold_over_the_range.c
void mark_one(int32 a[], int32 n, int32 i) {
    a[i] = 1;
}
```

```click
verifying "store_does_not_preserve_a_fold_over_the_range.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void mark_one(int32 a[], int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    requires n <= 1073741823;
    consumes a[0..n];
    produces a[0..n];
} by {
    mark entry;
    step();
    have icount(a, 0, n) == icount(at(entry, a), 0, n) by {
        simp();
    }
    execute();
    simp();
}
```

```expect
fail: a fact about `a` as a whole does not carry across the store to `a[i]`. Only a step the kernel proves leaves the whole object alone carries one, and a stated `separate(...)` is not read here.
```
