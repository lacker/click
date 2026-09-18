# a summarized loop inside a `branch` else arm

The same shape with the C loop written in the `if`'s else branch. Nothing about
the loop rule depends on the arm's polarity: the else arm reaches the loop, the
then arm is empty, and both join at the shared continuation.

```c filename=loop_inside_a_branch_else_arm.c
int32 count_down(int32 n) {
    int32 i;
    i = 0;
    if (n <= 0) {
    } else {
        while (i < n) {
            i = i + 1;
        }
    }
    return i;
}
```

```click
verifying "loop_inside_a_branch_else_arm.c";

int32 count_down(int32 n) {
    ensures result >= 0;
} by {
    step();
    step();
    branch {
        ensuring {
            fact i >= 0;
        }
        then {}
        else {
            loop {
                decreases n - i;
                invariant i >= 0;
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
