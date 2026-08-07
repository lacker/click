# returning branch arm

An arm that returns does not reach the shared continuation, so it closes its
own proof path. The proof after `branch` runs only on the arm that reaches it.

```c filename=returning_branch.c
int32 returning_branch(int32 x) {
    if (x < 0) {
        return 0;
    }
    return 1;
}
```

```click
verifying "returning_branch.c";

int32 returning_branch(int32 x) {
    ensures result >= 0 by {
        branch {
            then {
                step();
                simp();
            }
            else {
            }
        }
        step();
        simp();
    }
}
```

```expect
pass
```
