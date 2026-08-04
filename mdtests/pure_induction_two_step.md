# strong induction supports recursion by two

```click
function by_two(n: int32) -> int32
    decreases n
{
    if n <= 1 { 0 } else { by_two(n - 2) }
}

theorem by_two_is_zero(n: int32) {
    requires n >= 0;
    ensures by_two(n) == 0 by {
        induct(n) as ih;
        if n <= 1 {
            simp();
        } else {
            apply(ih(n - 2));
            simp();
        }
    }
}
```

```expect
pass
```
