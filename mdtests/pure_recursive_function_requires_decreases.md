# recursive pure functions require a decreases measure

```click
function missing(n: int32) -> int32 {
    if n <= 0 { 0 } else { missing(n - 1) }
}
```

```expect
fail: recursive pure function `missing` requires `decreases <int32 parameter>`
```
