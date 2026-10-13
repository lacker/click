# a step's `requires` entry must state an obligation the step leaves open

`b > 0` is not an obligation of this call, so its entry is refused where it is
written, and the diagnostic names the obligations the step does leave open.

```c filename=step_requires_that_matches_no_open_obligation.c
int32 first(int32 x, int32 y) {
    return x;
}

int32 caller(int32 a, int32 b) {
    return first(a, b);
}
```

```click
verifying "step_requires_that_matches_no_open_obligation.c";

int32 first(int32 x, int32 y) {
    requires x > 0 or y > 0;
    requires y > 0 or x > 0;
    ensures 1 == 1 by auto;
}

int32 caller(int32 a, int32 b) {
    requires a > 0;
    ensures 1 == 1 by {
        step() {
            requires b > 0 by simp;
        }
        step();
        simp();
    }
}
```

```expect
fail: `requires b > 0` matches no obligation this step leaves open
```
