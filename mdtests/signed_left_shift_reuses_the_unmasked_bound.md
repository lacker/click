# A signed left shift reuses a bound on the original count

```c filename=shifts.c
int32 shift32(int32 x, int32 s) {
    if (x > (2147483647 >> s)) return 0;
    return x << s;
}

int64 shift64(int64 x, int64 s) {
    return x << s;
}
```

```click
verifying "shifts.c";

int32 shift32(int32 x, int32 s) {
    requires x >= 0;
    requires s >= 0;
    requires s < 31;
    ensures true;
}

int64 shift64(int64 x, int64 s) {
    requires x >= 0i64;
    requires s >= 0i64;
    requires s < 64i64;
    requires x <= (9223372036854775807i64 >> s);
    ensures true;
}

theorem shift_count_mask(s: int32) {
    requires s >= 0;
    requires s < 32;
    ensures (s & 31) == s by close();
}

theorem shift_count_mask64(s: int64) {
    requires 0i64 <= s;
    requires s < 64i64;
    ensures (s & 63i64) == s by close();
}
```

```expect
pass
```
