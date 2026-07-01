# represented resource rejects bad origin

This checks that closing a represented resource proves its invariant. The code
keeps `write(flag[0..1])`, but it never establishes `flag[0] == 0`, so it
cannot close `uncalled(flag)`.

```c filename=init_bad.c
int32 init_bad(int32 flag[]) {
    return 0;
}
```

```click
affine resource uncalled(flag: int32*) {
    contains write(flag[0..1]);
    invariant flag[0] == 0;
}

verifying "init_bad.c";

int32 init_bad(int32 flag[]) {
    requires write(flag[0..1]);

    ensures uncalled(flag) by {
        symbolic_execute();
        close(uncalled(flag));
        close();
    }
}
```

```expect
fail: `close(uncalled(flag))` invariant failed
```
