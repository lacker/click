# A projection of a non-tuple is refused

`x.0` selects a tuple component; an `int32` has none.

```click
theorem not_a_tuple(x: int32) {
    ensures x.0 == x;
}
```

```expect
fail: `int32` is not a tuple, so it has no component 0
```
