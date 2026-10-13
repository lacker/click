# Constant wide narrowing past the upper bound wraps modulo 2^32

A `long` holding 2^32 returned from an `int` function keeps its low 32 bits,
0, as GCC and Clang do; no range is owed.
This test formerly pinned a refusal naming the range and value.

```c filename=constant_narrowing_wide_upper_wraps_modulo_2_to_the_32.c
int f(void) { long x = 4294967296L; return x; }
```

```click
verifying "constant_narrowing_wide_upper_wraps_modulo_2_to_the_32.c";
int32 f() { ensures result == 0; } by { execute(); simp(); }
```

```expect
pass
```
