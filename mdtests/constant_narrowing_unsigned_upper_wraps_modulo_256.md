# Constant unsigned narrowing past the upper bound wraps modulo 256

An `unsigned int` holding 300 converts to `unsigned char` as 44; no range is
owed.
This test formerly pinned a refusal naming the range and value.

```c filename=constant_narrowing_unsigned_upper_wraps_modulo_256.c
int f(void) { unsigned int x = 300; unsigned char y = x; return y; }
```

```click
verifying "constant_narrowing_unsigned_upper_wraps_modulo_256.c";
int32 f() { ensures result == 44; } by { execute(); simp(); }
```

```expect
pass
```
