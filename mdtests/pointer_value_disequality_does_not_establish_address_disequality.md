# Different pointer values need not have different numeric addresses

```click
theorem different_values(a: int32*, b: int32*) {
    requires a != b;
    ensures address(a) != address(b) by { close(); }
}
```

```expect
fail: requires the current goal as an available semantic fact
```
