# `step() by auto()` is refused as a removed spelling

`auto` is removed. A step's open obligations already go to the implicit
closer, so `by auto()` on a step meant `step()`; it is now refused with the
removal's refusal, which says to delete it.

```c filename=step_by_auto_is_refused.c
int32 compare_self(uint8 bytes[]) {
    return memcmp(bytes, bytes, 2);
}
```

```click
verifying "step_by_auto_is_refused.c";

int32 compare_self(uint8 bytes[]) {
    views bytes[0..2];
    ensures 1 == 1 by {
        step() by auto();
        step();
        close();
    }
}
```

```expect
fail: `auto()` is removed: a `by auto();` proof is the omitted proof, so delete it
```
