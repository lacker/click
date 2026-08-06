# preservation proof branches through one loop iteration

An explicit preservation proof can use the ordinary proof-level `if` and
branch-entry execution steps. Each proof branch must reach the loop back edge
and reestablish the complete invariant set.

```c filename=loop_preserve_branch.c
int32 loop_preserve_branch(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        if (i < 0) {
            i = 0;
        } else {
            i = i + 1;
        }
    }
    return i;
}
```

```click
verifying "loop_preserve_branch.c";

int32 loop_preserve_branch(int32 n) {
    requires n >= 0 and n <= 2147483647;
    ensures result == n;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;
        preserve by {
            if i < 0 {
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
    step();
    simp();
}
```

```expect
pass
```
