# C shifts

This checks the first C0 signed `int32` shift slice: `<<`, arithmetic `>>`,
C-like precedence, and pure Click functions using the same operators.

```c filename=shift_left_const.c
int32 shift_left_const() {
    return 3 << 2;
}
```

```c filename=shift_precedence.c
int32 shift_precedence() {
    return 1 << 2 + 1;
}
```

```c filename=shift_right_negative.c
int32 shift_right_negative() {
    return ~15 >> 2;
}
```

```c filename=shift_right_symbolic.c
int32 shift_right_symbolic(int32 x) {
    return x >> 2;
}
```

```click
verifying "shift_left_const.c";
verifying "shift_precedence.c";
verifying "shift_right_negative.c";
verifying "shift_right_symbolic.c";

function shl_const() -> int32 {
    3 << 2
}

function ashr2(x: int32) -> int32 {
    x >> 2
}

int32 shift_left_const() {
    ensures constant_shift: result == shl_const() by auto;
    ensures concrete_shift: result == 12 by auto;
}

int32 shift_precedence() {
    ensures addition_before_shift: result == 8 by auto;
}

int32 shift_right_negative() {
    ensures arithmetic_right_shift: result == ~3 by auto;
}

int32 shift_right_symbolic(int32 x) {
    ensures symbolic_right_shift: result == ashr2(x) by auto;
}
```

```expect
pass
```
