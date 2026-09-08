# Symbolic signed and unsigned wide values narrow only with proved bounds

```c filename=narrow.c
int signed_value(long value) { return value; }
int unsigned_value(unsigned long value) { return value; }
```

```click
verifying "narrow.c";
int signed_value(long value) {
    requires value >= -2147483648i64;
    requires value <= 2147483647i64;
    ensures result == (uint32)value;
} by { execute(); simp(); }
int unsigned_value(unsigned long value) {
    requires value <= 2147483647u64;
    ensures result == (uint32)value;
} by { execute(); simp(); }
```

```expect
pass
```
