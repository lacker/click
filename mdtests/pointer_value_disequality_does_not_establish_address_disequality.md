# Different pointer values need not have different numeric addresses

```click
theorem different_values(a: int32*, b: int32*) {
    requires a != b;
    ensures address(a) != address(b) by { known(); }
}
```

```expect
fail: could not close the current goal
```
