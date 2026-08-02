# Smart step uses the proof case condition

This checks that smart `step()` uses the exact condition introduced by a
proof-level `if` to enter the matching C arm.

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
            step();
            step();
            simp();
        } else {
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
