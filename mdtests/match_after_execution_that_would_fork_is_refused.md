# A `match` after execution that would fork is refused

After execution each live arm of a `match` is a separate outcome path, as each arm of a proof `if` or `cases` that forks is. Tactics written after the `match` would then be checked once per arm, so the `match` is refused; the tactics belong in the arms.

```c filename=match_after_execution_that_would_fork_is_refused.c
int read(int* p) { return *p; }
```

```click
verifying "match_after_execution_that_would_fork_is_refused.c";

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
    match old(c.model) {
        Tri::Zero => { have old(c.model) == Tri::Zero; },
        Tri::One => { have old(c.model) == Tri::One; },
        Tri::Other(value) => { have old(c.model) == Tri::Other(value); },
    }
    close();
}
```

```expect
fail: the arms of this proof `match` after execution do not rejoin
```
