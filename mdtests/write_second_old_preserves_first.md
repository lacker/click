# write_second preserves an untouched cell

This checks that `old(...)` can refer to pre-call memory in a postcondition.
Writing `p[1]` should not change `p[0]`.

```c filename=write_second_old.c
int32 write_second_old(int32* p) {
    p[1] = 9;
    return p[1];
}
```

```click
verifying "write_second_old.c";

int32 write_second_old(int32* p) {
    requires valid_range(p, 8);
    ensures writes_second: p[1] == 9 by auto;
    ensures preserves_first: p[0] == old(p[0]) by auto;
}
```

```expect
pass
```
