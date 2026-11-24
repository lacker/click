# Empty separate ranges do not distinguish their bases

```click
theorem empty(a: int32*, b: int32*) {
    requires separate(memory(a[0..0]), memory(b[0..0]));
    ensures a != b by {
        close();
    }
}
```

```expect
fail: requires the current goal as an available semantic fact
```
