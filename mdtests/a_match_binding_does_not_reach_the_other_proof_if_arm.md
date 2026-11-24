# A `match` binding does not reach the other proof `if` arm

A proof `match` whose arms reach function exit keeps its field bindings on
those finished paths only. The other arm of an enclosing proof `if` starts
in the scope the `if` was written in, so it cannot name `v`, bound in the
first arm.

```c filename=a_match_binding_does_not_reach_the_other_proof_if_arm.c
int read(int* p) { return *p; }
```

```click
verifying "a_match_binding_does_not_reach_the_other_proof_if_arm.c";

spec enum Tri { Zero, One, Other(int) }

resource cell(p: int*) {
    field model: Tri;
    owns p[0..1];
}

int read(int* p) {
    owns c: cell(p);
    ensures result == p[0];
} by {
    if (p[0] > 0) {
        match c.model {
            Tri::Zero => { step_until(function.exit); close(); },
            Tri::One => { step_until(function.exit); close(); },
            Tri::Other(v) => { step_until(function.exit); close(); },
        }
    } else {
        match c.model {
            Tri::Zero => { step_until(function.exit); close(); },
            Tri::One => { step_until(function.exit); close(); },
            Tri::Other(w) => { have v == v by close(); step_until(function.exit); close(); },
        }
    }
}
```

```expect
fail: unbound variable `v`
```
