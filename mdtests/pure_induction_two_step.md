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
        let ih = induct(n);
        if n <= 1 {
            unfold(by_two(n));
            close() using { n <= 1; };
        } else {
            have 0 <= to_integer(n - 2);
            have to_integer(n - 2) < to_integer(n);
            apply(ih(n - 2));
            unfold(by_two(n));
            rewrite(by_two(n - 2), 0);
            close();
        }
    }
}
```

```expect
pass
```
