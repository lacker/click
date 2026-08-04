# a recursive pure call must decrease

```click
function stuck(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { stuck(n) }
}
```

```expect
fail: recursive call `stuck` -> `stuck` must pass a nonnegative decreases measure strictly smaller than `n` on this path
```
