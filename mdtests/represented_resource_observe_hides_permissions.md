# represented resource observe hides permissions

This checks that `observe(resource)` exposes facts only. It does not unpack the
resource or expose contained write permission.

```c filename=write_flag_observed.c
int32 write_flag_observed(int32* flag) {
    flag[0] = 1;
    return flag[0];
}
```

```click
affine resource zero_flag(flag: int32*) {
    contains write(flag[0..1]);
    fact flag[0] == 0;
}

verifying "write_flag_observed.c";

int32 write_flag_observed(int32* flag) {
    requires zero_flag(flag);

    ensures zero_flag(flag) by {
        observe(zero_flag(flag));
        symbolic_execute();
    }
}
```

```expect
fail: missing resource `write(flag[0..1])`
```
