# A call result used in a condition gets a proof name

`if (classify(x))` never stores the callee's result in a named C object, so
the branch fact and the callee's guarantee are about a value the proof cannot
spell. `let r = step(classify(x), { });` names that value: the callee declares
no `produces` binder, so the same `let` that introduces a produced instance
introduces the call's scalar result instead. The name then works in `have`,
`rewrite`, and `normalize() using` premises on either side of the branch.

`return classify(x);` is the same shape with the result flowing to `result`.

```c filename=call_result_in_condition.c
int classify(int x) {
    if (x == 0) {
        return 0;
    }
    return 1;
}

int has_class(int x) {
    if (classify(x)) {
        return 1;
    }
    return 0;
}

int forward_class(int x) {
    return classify(x);
}
```

```click
verifying "call_result_in_condition.c";

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

int has_class(int x) {
    ensures classified(x) != 0 implies result == 1;
    ensures classified(x) == 0 implies result == 0;
} by {
    let r = step(classify(x), { });
    branch {
        then {
            step();
            have classified(x) != 0 by {
                simp() using { r != 0; r == classified(x); }
            }
            simp();
        }
        else {}
    }
    step();
    have classified(x) == 0 by {
        simp() using { r == 0; r == classified(x); }
    }
    simp();
}

int forward_class(int x) {
    ensures result == classified(x);
} by {
    let r = step(classify(x), { });
    step();
    have result == classified(x) by {
        rewrite(r == classified(x));
        normalize();
    }
    simp();
}
```

```expect
pass
```
