# A nested post-execution `match` arm checks its own case

Each arm of a `match` nested in a post-execution `if` arm runs only under its own constructor case. Here the `Other` arm claims the `Zero` case, which its path refutes, so the proof fails in that arm.

```c filename=a_nested_post_execution_match_arm_checks_its_own_case.c
int read(int* p) { return *p; }
```

```click
verifying "a_nested_post_execution_match_arm_checks_its_own_case.c";

spec enum Tri { Zero, One, Other(int) }

resource cell(p: int*) {
    field model: Tri;
    owns p[0..1];
}

int read(int* p) {
    owns c: cell(p);
    ensures result == p[0];
    ensures c.model == old(c.model);
} by {
    step_until(function.exit);
    if (result > 0) {
        match old(c.model) {
            Tri::Zero => { close(); },
            Tri::One => { close(); },
            Tri::Other(value) => { have old(c.model) == Tri::Zero; },
        }
    } else {
        close();
    }
}
```

```expect
fail: could not establish `old(c.model) == Tri::Zero()`
```
