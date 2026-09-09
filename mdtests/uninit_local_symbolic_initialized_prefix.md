# Symbolic reads from the initialized prefix remain valid

```c filename=t.c
int32 local_prefix(int32 i) {
    int32 a[3];
    a[0] = 1;
    a[1] = 2;
    return a[i];
}
```

```click
verifying "t.c";
int32 local_prefix(int32 i) {
    requires 0 <= i and i < 2;
    ensures result == 1 or result == 2 by {
        if i < 1 {
            have i <= 0 by { apply(int32_lt_successor_implies_le(i, 0)); }
            have i == 0 by simp;
            execute();
            simp();
        } else {
            have i <= 1 by { apply(int32_lt_successor_implies_le(i, 1)); }
            have i == 1 by simp;
            execute();
            simp();
        }
    }
}
```

```expect
pass
```
