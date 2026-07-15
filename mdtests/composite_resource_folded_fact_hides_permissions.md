# composite resource folded fact hides permissions

This checks that folded composite-resource facts are visible, but contained
write permission is still hidden until `unfold(...)`.

```c filename=write_flag_without_unfold.c
int32 write_flag_without_unfold(int32* flag) {
    flag[0] = 1;
    return flag[0];
}
```

```click
resource zero_flag(flag: int32*) {
    owns flag[0..1];
    fact flag[0] == 0;
}

verifying "write_flag_without_unfold.c";

int32 write_flag_without_unfold(int32* flag) {
    consumes zero_flag(flag);

    produces zero_flag(flag) by auto;
}
```

```expect
fail: missing resource fact `owns flag[0..1]`
```
