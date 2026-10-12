# An unconstrained pointer's address is not zero

```click
theorem unknown_address(p: int32*, x: uint64) {
    ensures address(p) + x == x by { normalize(); }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
