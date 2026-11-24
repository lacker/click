# A theorem cannot take a kernel law's name

`integer_range_fold_empty` is a law the kernel supplies, and citing it
applies that law. Before, a file theorem of that name was accepted, and a
citation applied the kernel law instead, so the second theorem verified
without meeting the file theorem's requirement `x == 5`.

```click
theorem integer_range_fold_empty(x: Integer) {
    requires x == 5;
    ensures x == 5 by close();
}

theorem uses(n: Integer) {
    ensures (0..0).fold(n, |acc, k| { acc + 1 }) == n by {
        apply(integer_range_fold_empty((0..0).fold(n, |acc, k| { acc + 1 })));
    }
}
```

```expect
fail: `integer_range_fold_empty` names a law the kernel supplies
```
