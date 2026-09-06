# A concrete callback may not require more than its named contract

The implementation requires `10 <= value`, but callers of `PositiveStep` are
only required to establish `0 <= input`. The function address therefore does
not satisfy the named contract, even though this particular call happens to
pass a value accepted by the implementation.

```c filename=strong_precondition_step.c
int32 increment_from_ten(int32 value) {
    return value + 1;
}
```

```c filename=apply_strong_precondition_step.c
int32 apply_step(int32 (*callback)(int32), int32 input) {
    return callback(input);
}
```

```c filename=strong_precondition_caller.c
int32 strong_precondition_caller() {
    return apply_step(&increment_from_ten, 41);
}
```

```click
verifying "strong_precondition_step.c";
verifying "apply_strong_precondition_step.c";
verifying "strong_precondition_caller.c";

contract int32 PositiveStep(int32 input) {
    requires 0 <= input;
    requires input <= 100;
    ensures result == input + 1;
}

int32 increment_from_ten(int32 value) {
    requires 10 <= value;
    requires value <= 100;
    ensures result == value + 1 by auto;
}

int32 apply_step(int32 (*callback)(int32), int32 input) {
    requires PositiveStep(callback);
    requires 0 <= input;
    requires input <= 100;
    ensures result == input + 1 by auto;
}

int32 strong_precondition_caller() {
    ensures result == 42 by auto;
}
```

```expect
fail: function `increment_from_ten` does not satisfy named contract `PositiveStep`
```
