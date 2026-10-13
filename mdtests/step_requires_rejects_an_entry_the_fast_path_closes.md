# a step's `requires` entry for an obligation the fast path closes is refused

After `have a > 0 or b > 0`, the first precondition is stated exactly, so the
fast path closes it and an entry for it is stale. It is refused, and the step
must be written with only the obligation that remains open.

```c filename=step_requires_rejects_an_entry_the_fast_path_closes.c
int32 first(int32 x, int32 y) {
    return x;
}

int32 caller(int32 a, int32 b) {
    return first(a, b);
}
```

```click
verifying "step_requires_rejects_an_entry_the_fast_path_closes.c";

int32 first(int32 x, int32 y) {
    requires x > 0 or y > 0;
    requires y > 0 or x > 0;
    ensures 1 == 1 by auto;
}

int32 caller(int32 a, int32 b) {
    requires a > 0;
    ensures 1 == 1 by {
        have a > 0 or b > 0 by simp;
        step() {
            requires a > 0 or b > 0 by simp;
            requires b > 0 or a > 0 by simp;
        }
        step();
        simp();
    }
}
```

```expect
fail: `requires a > 0 or b > 0` matches no obligation this step leaves open: its fast path already closes it
```
