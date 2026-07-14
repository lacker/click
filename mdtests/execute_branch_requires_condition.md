# execute branch requires its condition

This checks that explicit branch execution verifies the requested C arm rather
than trusting the proof script. The true proof case cannot execute the C else
arm.

```c filename=wrong_selected_branch.c
int32 wrong_selected_branch(int32 x) {
    if (x >= 0) {
        return 1;
    } else {
        return 0;
    }
}
```

```click
verifying "wrong_selected_branch.c";

int32 wrong_selected_branch(int32 x) {
    ensures result >= 0 by {
        if x >= 0 {
            execute_else_branch();
            simp();
        } else {
            execute_else_branch();
            simp();
        }
    }
}
```

```expect
fail: requested the else branch, but current pure facts prove the then branch
```
