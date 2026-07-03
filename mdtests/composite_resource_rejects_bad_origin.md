# composite resource rejects bad origin

This checks that packing a composite resource proves its fact. The code
keeps `write(flag[0..1])`, but it never establishes `flag[0] == 0`, so it
cannot pack `uncalled(flag)`.

```c filename=init_bad.c
int32 init_bad(int32 flag[]) {
    return 0;
}
```

```click
resource uncalled(flag: int32*) {
    contains write(flag[0..1]);
    fact flag[0] == 0;
}

verifying "init_bad.c";

int32 init_bad(int32 flag[]) {
    requires write(flag[0..1]);

    ensures uncalled(flag) by {
        symbolic_execute();
        pack(uncalled(flag));
    }
}
```

```expect
fail: `pack(uncalled(flag))` fact failed
```
