# Unfolding a fold-bodied function appends its last cell

With the nonempty range established, `unfold(f(args))` opens the append-last-cell
equation over the same function at the predecessor endpoint. Ordinary
obligations establish the law's remaining guards. The body reads the array,
and the C proof can name the last cell at its execution frontier.

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
    requires to_integer(n - 1) < 2147483647;
    views a[0..n];
    ensures icount(a, 0, n) == icount(a, 0, n - 1) + to_integer(a[n - 1]) by {
        step_until(function.exit);
        have 0 <= to_integer(n - 1);
        unfold(icount(a, 0, n));
        close();
    }
}
```

```expect
pass
```
