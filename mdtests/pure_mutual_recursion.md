# mutually recursive pure functions share decreasing natural measures

```click
function even(n: int32) -> int32
    decreases n
{
    if n <= 0 { 1 } else { odd(n - 1) }
}

function odd(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { even(n - 1) }
}

theorem four_is_even() {
    ensures even(4) == 1 by simp;
}

theorem three_is_odd() {
    ensures odd(3) == 1 by simp;
}
```

```expect
pass
```
