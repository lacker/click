# `known` does not close an implication whose consequent is not available

```click
theorem consequent_unknown(a: int32, b: int32) {
    requires b >= 0;
    ensures a > 3 implies b > 0 by { known(); }
}
```

```expect
fail: `known()` could not close the current goal
```
