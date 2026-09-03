# C0 rejects multiple unsequenced calls in one expression

C does not specify which of these calls runs first. C0 rejects the expression
instead of silently choosing an evaluation order that could change the
callee-visible state.

```c filename=unsequenced_calls.c
int32 unsequenced_calls(int32 value) {
    return first(value) + second(value);
}
```

```click
verifying "unsequenced_calls.c";

int32 unsequenced_calls(int32 value) {
    ensures result == 0 by auto;
}
```

```expect
fail: multiple unsequenced calls in one expression
```
