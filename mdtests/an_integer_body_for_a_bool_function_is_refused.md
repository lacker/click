# An integer body for a `bool` function is refused

A `-> bool` body produces only `bool` values. An integer is not read as a
truth value, so `1`, or a conditional with an integer branch, is a type
error rather than C's nonzero test.

```click
function flagged(x: int32) -> bool {
    if x > 0 { true } else { 0 }
}
```

```expect
fail: function `flagged` returns bool, but its body can produce `0` of type int32
```
