# Conditional contract requirement

A conditional expression in a contract requirement should be certified using
the condition's checked path facts, without asking the proof author to split
the contract into a single selected path.

```c filename=conditional_requires_expression.c
int32 conditional_requires_expression(int32 condition, int32 left, int32 right) {
    return 0;
}
```

```c filename=conditional_requires_expression_caller.c
int32 conditional_requires_expression_caller(int32 condition, int32 left, int32 right) {
    return conditional_requires_expression(condition, left, right);
}
```

```c filename=conditional_requires_load.c
int32 conditional_requires_load(int32 condition, int32 values[]) {
    return 0;
}
```

```c filename=conditional_requires_load_caller.c
int32 conditional_requires_load_caller(int32 condition, int32 values[]) {
    return conditional_requires_load(condition, values);
}
```

```click
verifying "conditional_requires_expression.c";
verifying "conditional_requires_expression_caller.c";
verifying "conditional_requires_load.c";
verifying "conditional_requires_load_caller.c";

int32 conditional_requires_expression(int32 condition, int32 left, int32 right) {
    requires (if condition != 0 { left } else { right }) == 7;
    ensures result == 0;
} by auto;

int32 conditional_requires_expression_caller(int32 condition, int32 left, int32 right) {
    requires (if condition != 0 { left } else { right }) == 7;
    ensures result == 0;
} by auto;

int32 conditional_requires_load(int32 condition, int32 values[]) {
    requires (if condition != 0 { values[0] } else { 0 }) == 7;
    views values[0..1];
    ensures result == 0;
} by auto;

int32 conditional_requires_load_caller(int32 condition, int32 values[]) {
    requires (if condition != 0 { values[0] } else { 0 }) == 7;
    views values[0..1];
    ensures result == 0;
} by auto;
```

```expect
pass
```
