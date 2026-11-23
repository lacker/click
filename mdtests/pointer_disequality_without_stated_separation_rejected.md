# A pointer disequality still needs evidence

```click
theorem missing(a: int32*, b: int32*) {
    ensures a != b by { known(); }
}
```

```expect
fail: could not close the current goal
```
