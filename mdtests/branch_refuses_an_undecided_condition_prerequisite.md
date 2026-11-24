# `branch` refuses a condition prerequisite it cannot decide

A non-constant `double` cast to `int32` in a C condition owes the cast's
lower and upper bounds. `branch` checks each prerequisite by exact lookup or
the kernel's condition decision. A `requires` or `have` can establish the
bounds before the branch splits.

```c filename=branch_float_cast_prerequisite.c
int32 positive(double d) {
    if ((int32) d > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "branch_float_cast_prerequisite.c";

int32 positive(double d) {
    ensures result >= 0;
} by {
    branch { true => { step(); close(); } false => {} }
    step();
    close();
}
```

```expect
fail: `branch` is missing condition prerequisite
```
