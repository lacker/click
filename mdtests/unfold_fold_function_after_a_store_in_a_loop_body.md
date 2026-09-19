# unfolding a fold-bodied function after a store into the range it reads

The loop body writes `a[i]`, a cell inside the range `icount` folds over. The
`unfold` runs after that store, so the fold's own read is evaluated at the
snapshot the store produced: one read per item of the range, at that snapshot,
with no case analysis over which item aliases the written cell. The append
law's last cell is then the value the store wrote, which is what makes the
equation this `have` states the one a reader would expect.

```c filename=unfold_fold_function_after_a_store_in_a_loop_body.c
void mark_prefix(int32 a[], int32 n) {
    for (int32 i = 0; i < n; i++) {
        a[i] = 1;
    }
}
```

```click
verifying "unfold_fold_function_after_a_store_in_a_loop_body.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, j| { acc + to_integer(p[j]) })
}

void mark_prefix(int32 a[], int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    requires loadable(a[0..n]);
    consumes a[0..n];
    produces a[0..n];
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        owns a[0..n];
        initialize by { simp(); }
        preserve by {
            have 0 <= i by { simp(); }
            have i < n by { simp(); }
            have i < 1073741823 by {
                arithmetic() using { i < n; n <= 1073741823; }
            }
            have i < 2147483647 by { arithmetic() using { i < 1073741823; } }
            step();
            have icount(a, 0, i + 1) == icount(a, 0, i) + to_integer(a[i]) by {
                unfold(icount(a, 0, i + 1)) using {
                    0 <= i;
                    i < 2147483647;
                }
                simp();
            }
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
