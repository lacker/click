# composite resource over memory

This checks the first composite-resource slice. `uncalled(flag)` wraps
owned memory for `flag[0..1]` plus the abstract fact that `flag[0] == 0`; `called(flag)`
wraps the same write permission plus the fact that `flag[0] == 1`.

```c filename=init_once.c
int32 init_once(int32 flag[]) {
    flag[0] = 0;
    return 0;
}
```

```c filename=complete_once.c
int32 complete_once(int32 flag[]) {
    if (flag[0] == 0) {
        flag[0] = 1;
        return flag[0];
    } else {
        return 0;
    }
}
```

```click
resource uncalled(flag: int32*) {
    owns flag[0..1];
    fact flag[0] == 0;
}

resource called(flag: int32*) {
    owns flag[0..1];
    fact flag[0] == 1;
}

verifying "init_once.c";
verifying "complete_once.c";

int32 init_once(int32 flag[]) {
    consumes flag[0..1];

    produces uncalled(flag) by {
        execute_rest();
        fold(uncalled(flag));
    }
}

int32 complete_once(int32 flag[]) {
    consumes uncalled(flag);

    produces called(flag) by {
        unfold(uncalled(flag));
        execute_rest();
        fold(called(flag));
    }

    ensures result == 1 by {
        unfold(uncalled(flag));
        execute_rest();
        fold(called(flag));
        simp();
    }
}
```

```expect
pass
```
