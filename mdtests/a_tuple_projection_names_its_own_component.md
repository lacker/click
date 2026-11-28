# A tuple projection names its own component

`(x, y).1` is `y`, not `x`: the claim that it is `x` is refused, and the
refusal spells the tuple and its projection as written.

```click
theorem wrong_component(x: int32, y: int32) {
    ensures (x, y).1 == x;
}
```

```expect
fail: could not establish `(x, y).1 == x`
```
