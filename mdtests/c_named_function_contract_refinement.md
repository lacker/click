# Concrete callbacks may refine a named contract

A concrete callback satisfies a named contract when callers of the named
contract establish enough to meet the callback's weaker requirements and the
callback establishes everything promised by the named contract. Parameter
names are binders: `input` and `value` need not have the same spelling.

```c filename=refining_step.c
int32 increment(int32 value) {
    return value + 1;
}
```

```c filename=apply_refining_step.c
int32 apply_step(int32 (*callback)(int32), int32 input) {
    int32 result;
    result = callback(input);
    return result;
}
```

```c filename=refining_step_caller.c
int32 refining_step_caller() {
    return apply_step(&increment, 41);
}
```

```click
verifying "refining_step.c";
verifying "apply_refining_step.c";
verifying "refining_step_caller.c";

contract int32 PositiveStep(int32 input) {
    requires 0 <= input;
    requires input <= 100;
    ensures result == input + 1;
    ensures 0 < result;
}

int32 increment(int32 value) {
    requires -100 <= value;
    requires value <= 1000;
    ensures result == value + 1 by auto;
    ensures value < result by auto;
}

int32 apply_step(int32 (*callback)(int32), int32 input) {
    requires PositiveStep(callback);
    requires 0 <= input;
    requires input <= 100;
    ensures result == input + 1 by auto;
    ensures 0 < result by auto;
}

int32 refining_step_caller() {
    ensures result == 42 by auto;
}
```

```expect
pass
```
