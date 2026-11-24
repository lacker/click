# A refused proof `if` case names its case

A proof-level `if y > 3` splits the proof of `result == 0` into two cases, and
neither proves it: the result is `x`. The refusal is the unclosed goal of the
first case, and its proof context names that case, `y > 3`, on a line of its
own, although the condition shares no term with the goal. The unrelated
`requires z > 3` stays out of the context, as does every other `requires` that
does not bear on the goal.

```c filename=a_refused_proof_if_case_names_its_case.c
int32 f(int32 x, int32 y, int32 z) {
    return x;
}
```

```click
verifying "a_refused_proof_if_case_names_its_case.c";

int32 f(int32 x, int32 y, int32 z) {
    requires x < 10;
    requires z > 3;
    ensures result == 0;
} by {
    if y > 3 {
        step_until(function.exit);
        close();
    } else {
        step_until(function.exit);
        close();
    }
}
```

```expect
fail: `ensures result == 0` failed for `f.ensures_0` path 0: unclosed goal: result == 0; left side evaluated to x, right side evaluated to 0
proof context for the goal:
  case: [y > 3]
  pure facts: [x < 10]
  resource facts: []
```
