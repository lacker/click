# well-founded pure recursion evaluates concrete arguments

The recursive edge is taken only when `n >= 1`, so `n - 1` is a
nonnegative measure strictly smaller than `n`.

```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}

theorem countdown_three_is_zero() {
    ensures countdown(3) == 0 by simp;
}
```

```expect
pass
```
