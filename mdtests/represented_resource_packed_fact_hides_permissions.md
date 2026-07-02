# represented resource packed fact hides permissions

This checks that packed represented-resource facts are visible, but contained
write permission is still hidden until `unpack(...)`.

```c filename=write_flag_without_unpack.c
int32 write_flag_without_unpack(int32* flag) {
    flag[0] = 1;
    return flag[0];
}
```

```click
affine resource zero_flag(flag: int32*) {
    contains write(flag[0..1]);
    fact flag[0] == 0;
}

verifying "write_flag_without_unpack.c";

int32 write_flag_without_unpack(int32* flag) {
    requires zero_flag(flag);

    ensures zero_flag(flag) by auto;
}
```

```expect
fail: missing resource `write(flag[0..1])`
```
