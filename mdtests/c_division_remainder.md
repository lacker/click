# C division and remainder

This checks C0 signed `int32` `/` and `%`: parser precedence, ordinary
results, negative truncation toward zero, and Surface Click functions using the
same operators.

```c filename=divide_known.c
int32 divide_known(int32 x) {
    return x / 2;
}
```

```c filename=remainder_known.c
int32 remainder_known(int32 x) {
    return x % 3;
}
```

```c filename=divide_constant.c
int32 divide_constant() {
    return 8 / 2;
}
```

```c filename=remainder_constant.c
int32 remainder_constant() {
    return 10 % 3;
}
```

```c filename=division_precedence.c
int32 division_precedence() {
    return 10 + 8 / 2 % 3;
}
```

```c filename=negative_division.c
int32 negative_division() {
    return ~9 / 2;
}
```

```click
verifying "divide_known.c";
verifying "remainder_known.c";
verifying "divide_constant.c";
verifying "remainder_constant.c";
verifying "division_precedence.c";
verifying "negative_division.c";

function half(int32 x) -> int32 {
    x / 2
}

function rem3(int32 x) -> int32 {
    x % 3
}

int32 divide_known(int32 x) {
    ensures symbolic_division: result == half(x) by auto;
}

int32 remainder_known(int32 x) {
    ensures symbolic_remainder: result == rem3(x) by auto;
}

int32 divide_constant() {
    ensures concrete_division: result == 4 by auto;
}

int32 remainder_constant() {
    ensures concrete_remainder: result == 1 by auto;
}

int32 division_precedence() {
    ensures division_before_addition: result == 11 by auto;
}

int32 negative_division() {
    ensures truncates_toward_zero: result == ~4 by auto;
}
```

```expect
pass
```
