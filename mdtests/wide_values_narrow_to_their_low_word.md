# Symbolic signed and unsigned wide values narrow to their low word

Returning a `long` or an `unsigned long` from an `int` function keeps the
value's low 32 bits, as GCC and Clang do, and owes no range: the result is
the same word as `(uint32)value` whatever the value.

```c filename=narrow.c
int signed_value(long value) { return value; }
int unsigned_value(unsigned long value) { return value; }
```

```click
verifying "narrow.c";
int signed_value(long value) {
    ensures result == (uint32)value;
} by { execute(); simp(); }
int unsigned_value(unsigned long value) {
    ensures result == (uint32)value;
} by { execute(); simp(); }
```

```expect
pass
```
