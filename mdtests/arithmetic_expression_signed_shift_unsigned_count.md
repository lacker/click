# Signed left shifts retain the unsigned count in their overflow check

```c filename=arithmetic.c
int32 shift32(int32 n, uint32 d) { return n << d; }
int64 shift64(int64 n, uint64 d) { return n << d; }
```

```click
verifying "arithmetic.c";

int32 shift32(int32 n, uint32 d) {
    requires d < 31u32;
    requires n >= 0;
    requires n <= (2147483647 >> d);
    ensures true;
}

int64 shift64(int64 n, uint64 d) {
    requires d < 63u64;
    requires n >= 0i64;
    requires to_integer(n) <= to_integer(9223372036854775807u64 >> d);
    ensures true;
}

theorem unsigned_count_mask(d: uint32) {
    requires d < 32u32;
    ensures (d & 31u32) == d by close();
}
```

```expect
pass
```
