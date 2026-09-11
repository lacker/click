# a structured call precondition is an emitted obligation, not a kernel search

The callee's precondition is a disjunction. The caller establishes one arm
exactly, and nothing else. The kernel no longer chooses the arm: its exact
routes do not cover a disjunction, so the call raises the precondition as a
required verification condition and the proof side discharges it with checked
evidence.

```c filename=either.c
int32 caller(int32 x, int32 y) {
    int32 result;
    result = either_positive(x, y);
    return result;
}
```

```click
verifying "either.c";

extern int32 either_positive(int32 x, int32 y) {
    requires x > 0 or y > 0;
    ensures result == 0;
}

int32 caller(int32 x, int32 y) {
    requires x > 0;
    ensures result == 0;
}
```

```expect
pass
```
