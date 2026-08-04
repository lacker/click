# the next recursive measure must be nonnegative

The negative base path of `countdown` is fine because it makes no recursive
call. `bad` recurses from that path and is rejected.

```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}

function bad(n: int32) -> int32
    decreases n
{
    if n <= 0 { bad(n - 1) } else { 0 }
}
```

```expect
fail: recursive call `bad` -> `bad` must pass a nonnegative decreases measure strictly smaller than `n` on this path
```
