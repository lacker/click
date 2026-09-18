# A fold binder is not the enclosing accumulator it shadows

Pure `.fold` binder names are local names, and the kernel gives each one a
variable id derived from the name, so two folds that write `|acc, k|` bind the
same id. That makes shadowing ordinary: an inner `|acc, j|` rebinds the name
its enclosing `|acc, k|` introduced, while an inner `|total, j|` leaves the
enclosing `acc` readable.

The two inner folds below therefore have the same spelling for their body,
`acc`, and mean different things by it. `nested_bound`'s inner fold returns its
own accumulator, so it returns its initial value `0` and the outer accumulator
counts up by one per step. `nested_free`'s inner fold returns the *enclosing*
accumulator, so the outer accumulator doubles its own step. At `lo = 0`,
`hi = 2` the two functions are `1` and `2`.

Nothing may equate them. A fold comparison that matches two occurrences merely
because they carry the same id would, since one occurrence is bound by the fold
being compared and the other is free in it.

```c filename=fold_binder_is_not_an_enclosing_accumulator.c
int32 fold_binder_is_not_an_enclosing_accumulator(int32 lo, int32 hi) {
    return 0;
}
```

```click
verifying "fold_binder_is_not_an_enclosing_accumulator.c";

function nested_free(lo: int32, hi: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        (lo..hi).fold(0, |total, j| { acc }) + 1
    })
}

function nested_bound(lo: int32, hi: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        (lo..hi).fold(0, |acc, j| { acc }) + 1
    })
}

int32 fold_binder_is_not_an_enclosing_accumulator(int32 lo, int32 hi) {
    ensures distinct_folds: nested_free(lo, hi) == nested_bound(lo, hi) by { execute(); simp(); }
}
```

```expect
fail: unclosed goal: nested_free(lo, hi) == nested_bound(lo, hi)
```
