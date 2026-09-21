# a switch does not end the recursion measure's walk

`decreases <int32 parameter>` has no verification condition behind it. The
walk over the body *is* the proof of descent: it carries a lower bound on the
measure along each path and checks every recursive edge against it. So a path
the walk stops following is a recursive call nothing checks.

`break` answered the empty list — right in a loop body, where the loop
discards its body's answer anyway, and wrong in a `switch`, where it is the
ordinary way a case ends. A `switch` then unioned its cases' answers and
nothing else, dropping the selector path that matches no case and runs no case
body at all. Either way the list came out empty, and an empty list propagates:
a sequence keeps it empty, and `if` and `while` iterate over it, so every
later branch and loop body in the function went unwalked.

    int32 spin(int32 n) {
        int32 result;
        result = 0;
        switch (n) {
            case 0:  break;
            default: break;
        }
        if (n > 0) {
            result = spin(n);        //  same argument — never descends
        }
        return result;
    }

`spin(1)` calls `spin(1)`, and `decreases n` verified. The `case 0: break;
default: break;` shape is ordinary C, and so is a `switch` with one returning
case and no `default`, which drops the fall-through path the same way.

Every way out of a `switch` now continues at the statement after it: a case
body that ends normally, a `break`, and — where no case matches and there is
no `default` — the selector path that runs no case body. A `break` carries the
bound it holds to the enclosing construct rather than vanishing, which is what
the split between continuing and broken paths is for. And a branch or loop
body is walked even where no path reaches it: an empty bound list compares
against nothing, so entering it adds the structural refusals and no bound
refusal, and the walk stays total over the body.

`descends_past_a_switch` beside it is the positive: the same `switch`, and a
recursive edge that does lower the measure.

```c filename=c_decreases_checks_past_a_switch.c
int32 spin_past_a_switch(int32 n) {
    int32 result;
    result = 0;
    switch (n) {
        case 0:
            break;
        default:
            break;
    }
    if (n > 0) {
        result = spin_past_a_switch(n);
    }
    return result;
}

int32 descends_past_a_switch(int32 n) {
    int32 result;
    result = 0;
    switch (n) {
        case 0:
            break;
        default:
            break;
    }
    if (n > 0) {
        result = descends_past_a_switch(n - 1);
    }
    return result;
}
```

```click
verifying "c_decreases_checks_past_a_switch.c";

int32 descends_past_a_switch(int32 n) {
    decreases n;
    ensures result == 0 by auto;
}

int32 spin_past_a_switch(int32 n) {
    decreases n;
    ensures result == 0 by auto;
}
```

```expect
fail: could not certify C termination: recursive call to `spin_past_a_switch` must pass `n - K` for a positive constant K
```
