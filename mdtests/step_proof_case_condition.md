# Frontier branch uses the C condition

This checks that `branch` derives its cases from the C condition at the
execution frontier, without restating that condition as a logical proof split.

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
        branch {
            then {
                step();
                simp();
            }
            else {
                step();
                simp();
            }
        }
    }
}
```

```expect
pass
```
