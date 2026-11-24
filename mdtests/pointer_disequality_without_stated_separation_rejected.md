# A pointer disequality still needs evidence

```click
theorem missing(a: int32*, b: int32*) {
    ensures a != b by { close(); }
}
```

```expect
fail: requires the current goal as an available semantic fact
```
