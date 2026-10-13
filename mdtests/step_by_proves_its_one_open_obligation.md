# a step's plain `by` proves the one obligation its fast path leaves open

`memcmp` requires each compared byte to be defined. The caller's `viewable`
range implies that, but no fact states the quantified requirement, so the call
step leaves exactly that obligation open. A plain `by` proves it at the step's
pre-state.

```c filename=step_by_proves_its_one_open_obligation.c
int32 compare_self(uint8 bytes[]) {
    return memcmp(bytes, bytes, 2);
}
```

```click
verifying "step_by_proves_its_one_open_obligation.c";

int32 compare_self(uint8 bytes[]) {
    requires viewable(bytes[0..2]);
    ensures 1 == 1 by {
        step() by { simp(); }
        step();
        simp();
    }
}
```

```expect
pass
```
