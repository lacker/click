# a step's plain `by` with no open obligation is refused as superfluous

The `return` step after the call has no obligation its fast path leaves open,
so a `by` on it is refused rather than kept as a stale proof.

```c filename=step_by_with_no_open_obligation_is_superfluous.c
int32 compare_self(uint8 bytes[]) {
    return memcmp(bytes, bytes, 2);
}
```

```click
verifying "step_by_with_no_open_obligation_is_superfluous.c";

int32 compare_self(uint8 bytes[]) {
    requires viewable(bytes[0..2]);
    ensures 1 == 1 by {
        step() by { simp(); }
        step() by { simp(); }
        simp();
    }
}
```

```expect
fail: this step's `by` is superfluous
```
