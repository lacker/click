# proof if inside have requires both cases

Every branch of case analysis inside `have` must establish the local fact.

```c filename=unproved_have_case.c
int32 unproved_have_case(int32 x) {
    return x;
}
```

```click
verifying "unproved_have_case.c";

int32 unproved_have_case(int32 x) {
    ensures result == x by {
        have x <= 0 by {
            if x <= 0 {
                simp();
            } else {
                simp();
            }
        }
        execute_step();
        simp();
    }
}
```

```expect
fail: `have` failed
```
