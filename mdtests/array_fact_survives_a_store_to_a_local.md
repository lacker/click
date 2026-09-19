# a fact about an array survives a step that cannot touch it

`i = i + 1` writes a local cell, in a block of its own. Nothing a function of
`a` can observe changes across it, so the argument `icount` folds over names
the same snapshot on both sides of the step and the fact is still the fact.
This is what a plain `a[0] == 5` has always done here; the array argument now
does it too.

```c filename=array_fact_survives_a_store_to_a_local.c
void bump(int32 a[], int32 n) {
    int32 i;
    i = 0;
    i = i + 1;
}
```

```click
verifying "array_fact_survives_a_store_to_a_local.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void bump(int32 a[], int32 n) {
    requires 0 < n;
    requires a[0] == 5;
    views a[0..n];
} by {
    step();
    step();
    have a[0] == 5 by { simp(); }
    have 0 <= 0 by { simp(); }
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    step();
    have a[0] == 5 by { simp(); }
    have icount(a, 0, 0) == 0 by { simp(); }
    execute();
    simp();
}
```

```expect
pass
```
