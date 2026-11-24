# A named call result cannot be claimed equal to the wrong value

`let { result: r } = step(classify);` names the call's scalar result, and the
callee's guarantee constrains that name and nothing else. A `have` that
claims the named result equals a different value fails at the claim: the
result rewrites to what the callee guaranteed, and the remaining equation is
false.

```c filename=call_result_wrong_value.c
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
```

```click
verifying "call_result_wrong_value.c";

function classified(x: int32) -> int32 {
    if x == 0 { 0 } else { 1 }
}

int classify(int x) {
    ensures result == classified(x);
} by {
    branch {
        true => {
            step();
            have result == classified(x) by {
                unfold(classified(x));
                normalize() using { x == 0; };
            }
            close();
        }
        false => {}
    }
    step();
    have result == classified(x) by {
        unfold(classified(x));
        normalize() using { not(x == 0); };
    }
    close();
}

int has_class(int x) {
    ensures classified(x) != 0 implies result == 1;
    ensures classified(x) == 0 implies result == 0;
} by {
    let { result: r } = step(classify);
    have r == classified(x) + 1 by {
        rewrite(r, classified(x));
        normalize();
    }
    branch { true => { step(); close(); } false => {} }
    step();
    close();
}
```

```expect
fail: `normalize` goal did not normalize to true
```
