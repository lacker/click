# a step's `requires` entries prove each obligation its fast path leaves open

Each precondition of `first` is a disjunction the caller's `a > 0` implies but
no fact states, so the call step leaves both open. One `requires` entry per
obligation proves it at the step's pre-state, and the step then runs with every
obligation stated exactly.

```c filename=step_requires_proves_each_open_obligation.c
int32 first(int32 x, int32 y) {
    return x;
}

int32 caller(int32 a, int32 b) {
    return first(a, b);
}
```

```click
verifying "step_requires_proves_each_open_obligation.c";

int32 first(int32 x, int32 y) {
    requires x > 0 or y > 0;
    requires y > 0 or x > 0;
    ensures 1 == 1 by auto;
}

int32 caller(int32 a, int32 b) {
    requires a > 0;
    ensures 1 == 1 by {
        step() {
            requires a > 0 or b > 0 by simp;
            requires b > 0 or a > 0 by simp;
        }
        step();
        simp();
    }
}
```

```expect
pass
```
