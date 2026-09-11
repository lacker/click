# A summation fold needs bounds for every array element

The exact fold remains the postcondition, but the entry contract omits the
element range.  The proof must stop at the checked machine addition instead of
assigning a modular value to an overflowing prefix.

```c filename=integer_sum_range_fold_missing_bounds.c
int32 sum(int32 a[], int32 n) {
    int32 total;
    int32 i;
    total = 0;
    i = 0;
    while (i < n) {
        total = total + a[i];
        i = i + 1;
    }
    return total;
}
```

```click
verifying "integer_sum_range_fold_missing_bounds.c";

int32 sum(int32 a[], int32 n) {
    requires 0 <= n and n <= 1000;
    requires loadable(a[0..n]);
    views a[0..n];
    requires n == 2;
    requires a[0] == 2147483647;
    requires a[1] == 1;
    ensures result_sum: to_integer(result) ==
        (0..n).fold(0, |acc, k| { acc + to_integer(a[k]) }) by {
        execute();
        simp();
    }
}
```

```expect
fail: undefined behavior: signed overflow
```
