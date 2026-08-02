# explicit branch execution

This checks proof-level case analysis together with explicit execution of a
selected C `if` arm. Each proof case establishes the C condition, enters its
arm, executes the arm assignment, and then derives the bound needed for the
following potentially overflowing increment.

```c filename=increment_nonnegative.c
int32 increment_nonnegative(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
```

```click
verifying "increment_nonnegative.c";

int32 increment_nonnegative(int32 x) {
    requires x < 2147483647;

    ensures result > 0 by {
        step();
        if x >= 0 {
            step();
            step();
            have y < 2147483647 by simp;
            step();
            step();
            simp();
        } else {
            step();
            step();
            have y < 2147483647 by simp;
            step();
            step();
            simp();
        }
    }
}
```

```expect
pass
```
