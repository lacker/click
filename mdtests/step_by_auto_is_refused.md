# `step() by auto` is refused because it means `step()`

A step's open obligations already go to `auto`, so writing `by auto` on a step
adds nothing and is refused.

```c filename=step_by_auto_is_refused.c
int32 compare_self(uint8 bytes[]) {
    return memcmp(bytes, bytes, 2);
}
```

```click
verifying "step_by_auto_is_refused.c";

int32 compare_self(uint8 bytes[]) {
    requires viewable(bytes[0..2]);
    ensures 1 == 1 by {
        step() by auto;
        step();
        simp();
    }
}
```

```expect
fail: `step() by auto` is `step()`
```
