# pure theorem instantiate requires guard evidence

Specialization must still reject a universal fact when its instantiated guard
does not follow from the explicitly listed premises.

```click
theorem bounded_value(value: int32, limit: int32) {
    requires bounded: forall (k: int32) {
        0 <= k and k < limit implies k <= value
    };

    ensures 2 <= value by {
        instantiate(forall (k: int32) {
            0 <= k and k < limit implies k <= value
        }, 2) using {}
        assumption();
    }
}
```

```expect
fail: does not follow from the listed evidence
```
