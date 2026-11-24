# Casts preserve their native signedness

A same-width signed-to-unsigned cast does not preserve a negative Integer.

```click quick-solve
theorem wrong(x: int128) {
    requires to_integer(x) == -1;
    ensures to_integer(x as uint128) == -1 by close();
}
```

```expect
fail: could not establish
```
