# a step's plain `by` with two open obligations lists them as `requires` entries

A plain `by` proves a step's one open obligation. This call leaves two open, so
the step is refused, and the diagnostic spells each obligation as a `requires`
entry to copy.

```c filename=step_by_with_two_open_obligations_lists_them.c
int32 first(int32 x, int32 y) {
    return x;
}

int32 caller(int32 a, int32 b) {
    return first(a, b);
}
```

```click
verifying "step_by_with_two_open_obligations_lists_them.c";

int32 first(int32 x, int32 y) {
    requires x > 0 or y > 0;
    requires y > 0 or x > 0;
    ensures 1 == 1 by auto;
}

int32 caller(int32 a, int32 b) {
    requires a > 0;
    ensures 1 == 1 by {
        step() by { simp(); }
        step();
        simp();
    }
}
```

```expect
fail: this step leaves 2 open; write one `requires` entry for each
```
