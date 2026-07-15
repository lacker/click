# composite resource observe hides permissions

This checks that `observe(resource)` exposes the immediate view only. It does
not unfold the resource or expose contained write permission.

```c filename=write_flag_observed.c
int32 write_flag_observed(int32* flag) {
    flag[0] = 1;
    return flag[0];
}
```

```click
resource zero_flag(flag: int32*) {
    contains write(flag[0..1]);
    fact flag[0] == 0;
}

verifying "write_flag_observed.c";

int32 write_flag_observed(int32* flag) {
    consumes zero_flag(flag);

    produces zero_flag(flag) by {
        observe(zero_flag(flag));
        symbolic_execute();
    }
}
```

```expect
fail: missing resource fact `write(flag[0..1])`
```
