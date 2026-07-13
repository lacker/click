# proof if cases

This checks proof-level case analysis independently of C execution, after C
execution using `result`, and before C execution with each case running its own
symbolic execution.

```c filename=sign_after_execution.c
int32 sign_after_execution(int32 x) {
    return x;
}
```

```c filename=sign_before_execution.c
int32 sign_before_execution(int32 x) {
    return x;
}
```

```click
theorem int32_sign_split(x: int32) {
    ensures x <= 0 or x > 0 by {
        if x <= 0 {
            simp();
        } else {
            simp();
        }
    }
}

verifying "sign_after_execution.c";
verifying "sign_before_execution.c";

int32 sign_after_execution(int32 x) {
    ensures result <= 0 or result > 0 by {
        execute_rest();
        if result <= 0 {
            simp();
        } else {
            simp();
        }
    }
}

int32 sign_before_execution(int32 x) {
    ensures result <= 0 or result > 0 by {
        if x <= 0 {
            execute_rest();
            simp();
        } else {
            execute_rest();
            simp();
        }
    }
}
```

```expect
pass
```
