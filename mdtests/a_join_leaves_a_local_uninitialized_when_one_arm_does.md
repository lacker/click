# A local one arm never initialized is uninitialized after the join

Only the `then` arm of the C `if` gives `t` a value. On the path through the
`else` arm `t` was never written, so after the arms join, reading `t` is as
undefined as it was on that path, and the `return t` is refused.

The arm that did initialize `t` does not carry its value past the join. If
it did, the two arms would describe `t` differently and could not be joined
at all; that used to make the automatic loop closer walk such arms as
separate paths.

```c filename=a_join_leaves_a_local_uninitialized_when_one_arm_does.c
int32 maybe(int32 x) {
    int32 t;
    if (x == 3) {
        t = 1;
    }
    return t;
}
```

```click
verifying "a_join_leaves_a_local_uninitialized_when_one_arm_does.c";

int32 maybe(int32 x) {
    ensures result == 1 or result != 1;
} by {
    step();
    branch {
        true => {
            step();
        }
        false => {
        }
    }
    step();
    close();
}
```

```expect
fail: read of uninitialized storage
```
