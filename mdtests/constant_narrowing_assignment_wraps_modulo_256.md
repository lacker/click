# Constant narrowing at an assignment wraps modulo 256

Assigning the constant `-56` to an `unsigned char` stores 200, as GCC and
Clang do; no range is owed.
This test formerly pinned a refusal naming the range and value.

```c filename=constant_narrowing_assignment_wraps_modulo_256.c
int f(void) { int x = -56; unsigned char c = 0; c = x; return c; }
```

```click
verifying "constant_narrowing_assignment_wraps_modulo_256.c";
int32 f() { ensures result == 200; } by { execute(); simp(); }
```

```expect
pass
```
