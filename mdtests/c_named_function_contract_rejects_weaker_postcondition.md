# A concrete callback may not guarantee less than its named contract

The implementation only exposes that its result is greater than its argument.
Its C body happens to add one, but callers through `PositiveStep` may rely only
on the verified callback contract, not on an implementation body Click did not
put in that interface.

```c filename=weak_postcondition_step.c
int32 increasing(int32 value) {
    return value + 1;
}
```

```c filename=apply_weak_postcondition_step.c
int32 apply_step(int32 (*callback)(int32), int32 input) {
    return callback(input);
}
```

```c filename=weak_postcondition_caller.c
int32 weak_postcondition_caller() {
    return apply_step(&increasing, 41);
}
```

```click
verifying "weak_postcondition_step.c";
verifying "apply_weak_postcondition_step.c";
verifying "weak_postcondition_caller.c";

contract int32 PositiveStep(int32 input) {
    requires 0 <= input;
    requires input <= 100;
    ensures result == input + 1;
}

int32 increasing(int32 value) {
    requires 0 <= value;
    requires value <= 100;
    ensures value < result by auto;
}

int32 apply_step(int32 (*callback)(int32), int32 input) {
    requires PositiveStep(callback);
    requires 0 <= input;
    requires input <= 100;
    ensures result == input + 1 by auto;
}

int32 weak_postcondition_caller() {
    ensures result == 42 by auto;
}
```

```expect
fail: function `increasing` does not satisfy named contract `PositiveStep`
```
