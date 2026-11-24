# A `match` in a post-execution `if` arm takes each path's arm

A proof `match` written inside an arm of a post-execution `if` is decided per outcome path, as the `if` is: each path that reaches the `if` arm takes the `match` arm its constructor case selects, and the `Other` arm proves a fact about its own field binding.

```c filename=a_match_in_a_post_execution_if_arm_takes_each_paths_arm.c
int read(int* p) { return *p; }
```

```click
verifying "a_match_in_a_post_execution_if_arm_takes_each_paths_arm.c";

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
            Tri::Other(value) => { have old(c.model) == Tri::Other(value); },
        }
    } else {
        close();
    }
}
```

```expect
pass
```
