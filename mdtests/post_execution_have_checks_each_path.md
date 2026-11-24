# A have after a branch is checked on the arm's own path

A proof is at one program point at a time, so a `have` about `result` is
checked on the path where it is written. Here `branch` splits at the C `if`,
each arm steps to exit with `step_until(function.exit)`, and each states
`result == 1`. It holds on the arm that returns `1` and is refused on the arm
that returns `0`.

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
    branch {
        true => {
            step_until(function.exit);
            have result == 1 by close();
        }
        false => {
            step_until(function.exit);
            have result == 1 by close();
        }
    }
}
```

```expect
fail: could not establish `result == 1`
```
