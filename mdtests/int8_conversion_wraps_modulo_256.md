# Conversion to `signed char` wraps modulo 256

GCC and Clang convert an `int` outside `-128..127` to `signed char` by
reducing it modulo 256 into that range, the implementation-defined result
they document. Click gives every conversion that value, written or implicit,
and owes no range: 200 becomes -56 and -129 becomes 127.
`mdtests/int8_narrowing_equals_its_source_only_in_range.md` shows that the
unwrapped value is no longer claimed.

```c filename=int8_conversion_wraps_modulo_256.c
signed char cast(int x) { return (signed char)x; }
signed char returned(int x) { return x; }
int initialized(int x) { signed char c = x; return c; }
int assigned(int x) { signed char c; c = x - 1; return c; }
```

```click
verifying "int8_conversion_wraps_modulo_256.c";

signed char cast(int32 x) {
    requires x == 200;
    ensures result == -56;
} by { execute(); simp(); }

signed char returned(int32 x) {
    requires x == -129;
    ensures result == 127;
} by { execute(); simp(); }

int32 initialized(int32 x) {
    requires x == 383;
    ensures result == 127;
} by { execute(); simp(); }

int32 assigned(int32 x) {
    requires x == 129;
    ensures result == -128;
} by { execute(); simp(); }
```

```expect
pass
```
