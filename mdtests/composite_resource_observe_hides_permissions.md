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
    owns flag[0..1];
    fact flag[0] == 0;
}

verifying "write_flag_observed.c";

int32 write_flag_observed(int32* flag) {
    consumes zero_flag(flag);

    produces zero_flag(flag) by {
        observe(zero_flag(flag));
        execute();
    }
}
```

```expect
fail: missing resource fact `owns flag[0..1]`
```
