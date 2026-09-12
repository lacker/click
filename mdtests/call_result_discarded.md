# A discarded call result cannot be named

`let name = step(...)` names the scalar result of a call whose result the C
uses. A call in statement position discards its result and assigns nothing, so
there is no value to name and the step is refused where it is written rather
than binding an unconstrained name.

```c filename=call_result_discarded.c
int classify(int x) {
    if (x == 0) {
        return 0;
    }
    return 1;
}

int ignore_class(int x) {
    classify(x);
    return 0;
}
```

```click
verifying "call_result_discarded.c";

function classified(x: int32) -> int32 {
    if x == 0 { 0 } else { 1 }
}

int classify(int x) {
    ensures result == classified(x);
} by {
    branch {
        then {
            step();
            have result == classified(x) by {
                unfold(classified(x));
                normalize() using { x == 0; }
            }
            simp();
        }
        else {}
    }
    step();
    have result == classified(x) by {
        unfold(classified(x));
        normalize() using { not(x == 0); }
    }
    simp();
}

int ignore_class(int x) {
    ensures result == 0;
} by {
    let r = step(classify(x), { });
    execute();
    simp();
}
```

```expect
fail: names a call result, but this call's result is unused
```
