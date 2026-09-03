# C conditional expressions and scalar casts

This checks C0's scalar conditional operator, including short-circuit branch
selection, and explicit int32/uint8 casts with the existing byte-range proof
obligations.

```c filename=choose_left.c
int32 choose_left(int32 condition, int32 left, int32 right) {
    return condition ? left : right;
}
```

```c filename=choose_right.c
int32 choose_right(int32 condition, int32 left, int32 right) {
    return condition ? left : right;
}
```

```c filename=conditional_short_circuit.c
int32 conditional_short_circuit(int32 condition) {
    return condition ? 7 : 1 / 0;
}
```

```c filename=cast_byte.c
uint8 cast_byte(int32 value) {
    return (uint8)value;
}
```

```c filename=promote_byte.c
int32 promote_byte(uint8 value) {
    return (int32)value + 1;
}
```

```click
verifying "choose_left.c";
verifying "choose_right.c";
verifying "conditional_short_circuit.c";
verifying "cast_byte.c";
verifying "promote_byte.c";

int32 choose_left(int32 condition, int32 left, int32 right) {
    requires condition != 0;
    ensures selected_then: result == left by auto;
}

int32 choose_right(int32 condition, int32 left, int32 right) {
    requires condition == 0;
    ensures selected_else: result == right by auto;
}

int32 conditional_short_circuit(int32 condition) {
    requires condition != 0;
    ensures selected_without_evaluating_else: result == 7 by auto;
}

uint8 cast_byte(int32 value) {
    requires value >= 0;
    requires value <= 255;
    ensures checked_cast: result == value by auto;
}

int32 promote_byte(uint8 value) {
    ensures promoted_cast: result == value + 1 by auto;
}
```

```expect
pass
```
