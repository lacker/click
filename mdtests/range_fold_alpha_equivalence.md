# Symbolic folds ignore binder names

This checks that Kernel Click treats pure `.fold` binder names as local names.
Two folds with the same bounds, initial value, and body shape should compare
equal even when one uses `|acc, k|` and the other uses `|total, i|`.

```c filename=range_fold_alpha_equivalence.c
int32 range_fold_alpha_equivalence(int32 lo, int32 hi) {
    return 0;
}
```

```click
verifying "range_fold_alpha_equivalence.c";

function sum_range_a(lo: int32, hi: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + k
    })
}

function sum_range_b(lo: int32, hi: int32) -> int32 {
    (lo..hi).fold(0, |total, i| {
        total + i
    })
}

int32 range_fold_alpha_equivalence(int32 lo, int32 hi) {
    ensures renamed_fold_binders: sum_range_a(lo, hi) == sum_range_b(lo, hi) by { execute(); simp(); }
}
```

```expect
pass
```
