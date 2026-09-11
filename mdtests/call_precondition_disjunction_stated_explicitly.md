# a structured call precondition can be stated before the call

The same callee and caller as
`call_precondition_disjunction_is_an_obligation`, with the precondition
stated as an explicit `have` ahead of the step. The stated fact is then
exactly available, so the call raises no verification condition at all: the
kernel's exact route discharges it and nothing searches.

```c filename=stated.c
int32 caller(int32 x, int32 y) {
    int32 result;
    result = either_positive(x, y);
    return result;
}
```

```click
verifying "stated.c";

extern int32 either_positive(int32 x, int32 y) {
    requires x > 0 or y > 0;
    ensures result == 0;
}

int32 caller(int32 x, int32 y) {
    requires x > 0;
    ensures result == 0 by {
        have x > 0 or y > 0 by { left(); assumption(); }
        step();
        step();
        step();
        assumption();
    }
}
```

```expect
pass
```
