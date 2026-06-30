# write_second does not keep an overwritten cell

This checks that `old(...)` distinguishes the pre-call value from the
post-call value when a function writes that cell.

```c filename=write_second_bad_old.c
int32 write_second_bad_old(int32* p) {
    p[1] = 9;
    return p[1];
}
```

```click
verifying "write_second_bad_old.c";

int32 write_second_bad_old(int32* p) {
    requires valid_range(p, 8);
    requires write(p[1..2]);
    ensures keeps_second: p[1] == old(p[1]) by auto;
}
```

```expect
fail: left side evaluated to Int32(Constant(9))
```
