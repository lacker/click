# Post-execution have checks every path

A `have` after batch execution must hold on every completed return path, not
only the first symbolic outcome.

```c filename=post_have_each_path.c
int32 branch_value(int32 flag) {
    if (flag) {
        return 1;
    } else {
        return 0;
    }
}
```

```click
verifying "post_have_each_path.c";

int32 branch_value(int32 flag) {
    ensures result >= 0;
} by {
    execute();
    have result == 1 by simp;
    simp();
}
```

```expect
fail: `have` failed
```
