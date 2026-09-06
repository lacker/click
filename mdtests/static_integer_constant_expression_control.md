# static integer initializers support comparisons, control, and casts

Static integer initializers may use bounded comparisons, short-circuit logical
operators, selected conditional branches, and checked integer casts. These
forms are folded before static storage is materialized, so an unselected
divide-by-zero branch is never evaluated.

```c filename=static_integer_constant_expression_control.c
int32 values[5] = {
    1 < 2,
    (0 && (1 / 0)) ? 10 : 20,
    (1 || (1 / 0)) ? 30 : 40,
    ((3 == 3) && (4 != 5)) ? (uint8) 255 : 0,
    (int16) (6 * 7)
};
static int32 private_value = (2 <= 2) + (4 >= 4) + (0 ? (1 / 0) : (4 > 3));
static int32 mixed_value = (-1 < 1u) ? 2 : 1;

int32 read() {
    static uint16 local_value = (uint16) ((3 < 4) ? 9 : (1 / 0));
    return values[0] + values[1] + values[2] + values[3] + values[4]
        + private_value + mixed_value + local_value;
}
```

```click
verifying "static_integer_constant_expression_control.c";

int32 read() {
    ensures result == 361 by auto;
}
```

```expect
pass
```
