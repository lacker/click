# Scalar induction can follow earlier helper facts

Helper facts may precede scalar induction. The hypothesis becomes available
when `induct` executes and still states the same theorem at smaller arguments.

```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}

theorem countdown_is_zero(n: int32) {
    requires n >= 0;
    ensures countdown(n) == 0 by {
        have n == n;
        have 0 <= to_integer(n);
        let ih = induct(n);
        if n <= 0 {
            unfold(countdown(n));
            close() using { n <= 0; };
        } else {
            have 0 <= to_integer(n - 1);
            have to_integer(n - 1) < to_integer(n);
            apply(ih(n - 1));
            unfold(countdown(n));
            rewrite(countdown(n - 1), 0);
            close();
        }
    }
}
```

```expect
pass
```
