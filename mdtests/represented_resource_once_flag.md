# represented affine resource over memory

This checks the first represented-resource slice. `uncalled(flag)` wraps
`write(flag[0..1])` plus the abstract fact that `flag[0] == 0`; `called(flag)`
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
affine resource uncalled(flag: int32*) {
    contains write(flag[0..1]);
    invariant flag[0] == 0;
}

affine resource called(flag: int32*) {
    contains write(flag[0..1]);
    invariant flag[0] == 1;
}

verifying "init_once.c";
verifying "complete_once.c";

int32 init_once(int32 flag[]) {
    requires write(flag[0..1]);

    ensures uncalled(flag) by {
        symbolic_execute();
        close(uncalled(flag));
    }
}

int32 complete_once(int32 flag[]) {
    requires uncalled(flag);

    ensures called(flag) by {
        open(uncalled(flag));
        symbolic_execute();
        close(called(flag));
    }

    ensures result == 1 by {
        open(uncalled(flag));
        symbolic_execute();
        close(called(flag));
        simp();
    }
}
```

```expect
pass
```
