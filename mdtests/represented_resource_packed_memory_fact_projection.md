# represented resource packed memory fact projection

This checks that holding a packed represented resource exposes its memory facts
without unpacking the contained write permission.

```c filename=noop_flag.c
int32 noop_flag(int32* flag) {
    return 0;
}
```

```click
resource zero_flag(flag: int32*) {
    contains write(flag[0..1]);
    fact flag[0] == 0;
}

verifying "noop_flag.c";

int32 noop_flag(int32* flag) {
    requires zero_flag(flag);

    ensures flag[0] == 0 by auto;
    ensures zero_flag(flag) by auto;
}
```

```expect
pass
```
