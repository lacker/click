# C multiplication

This checks the first executable C multiplication slice: parsing precedence,
ordinary `int32` results, Surface Click postconditions using `*`, and signed
overflow as undefined behavior.

```c filename=multiply.c
int32 multiply_known(int32 x) {
    return x * 2;
}
```

```c filename=multiply_precedence.c
int32 multiply_precedence() {
    return 2 + 3 * 4;
}
```

```c filename=multiply_overflow.c
int32 multiply_overflow() {
    return 2147483647 * 2;
}
```

```click
verifying "multiply.c";
verifying "multiply_precedence.c";
verifying "multiply_overflow.c";

int32 multiply_known(int32 x) {
    requires x == 3;
    ensures symbolic_product: result == x * 2 by auto;
    ensures concrete_product: result == 6 by auto;
}

int32 multiply_precedence() {
    ensures precedence: result == 14 by auto;
}

int32 multiply_overflow() {
    ensures no_wrapping_result: result == 0 by auto;
}
```

```expect
fail: outcome was UndefinedBehavior(SignedOverflow)
```
