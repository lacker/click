# unfolding a fold-bodied function appends its last cell

With the two append guards listed, `unfold(f(args)) using { ... }` opens the
append-last-cell equation instead: `f(.., hi)` equals `f(.., hi - 1)` plus the
fold's body at `hi - 1`. The split endpoint is the fold's own end minus one; it
is not named separately, because the guards the kernel law needs at that
endpoint are exactly the `lo <= hi - 1` and `hi - 1 < 2147483647` a reader
would write anyway.

Both sides are the same function, so the shorter range is still described by
`icount`, not by a retyped fold. The range is symbolic at both ends and the
body reads the array. This is a C proof, which is where the last cell can also
be written down at the proof site.

```c filename=unfold_fold_function_appends_last_cell.c
int32 prefix_sum_equation(int32 a[], int32 n) {
    return 0;
}
```

```click
verifying "unfold_fold_function_appends_last_cell.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

int32 prefix_sum_equation(int32 a[], int32 n) {
    requires 0 < n;
    requires n - 1 < 2147483647;
    requires loadable(a[0..n]);
    views a[0..n];
    ensures icount(a, 0, n) == icount(a, 0, n - 1) + to_integer(a[n - 1]) by {
        execute();
        have 0 <= n - 1 by { simp(); }
        unfold(icount(a, 0, n)) using {
            0 <= n - 1;
            n - 1 < 2147483647;
        }
        simp();
    }
}
```

```expect
pass
```
