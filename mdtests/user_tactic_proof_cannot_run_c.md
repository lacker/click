# a tactic's proof cannot run C

A tactic runs no code, so its proof works at one point: it folds, unfolds,
applies, and proves facts. A `step()` in it is refused when the tactic is
declared.

```c filename=user_tactic_proof_cannot_run_c.c
struct pr { int32 a; int32 b; };

void user(struct pr *p) {
}
```

```click
verifying "user_tactic_proof_cannot_run_c.c";

resource both(p: struct pr*) {
    field tag: int32;
    owns p->a;
    owns p->b;
}

resource first(p: struct pr*) {
    field tag: int32;
    owns p->a;
}

resource second(p: struct pr*) {
    field tag: int32;
    owns p->b;
}


tactic stepping(p: struct pr*) {
    owns x: both(p);
    ensures 1 == 1;
} by {
    step();
}

void user(struct pr* p) {
    owns x: both(p);
} by {
    step();
    step();
    close();
}
```

```expect
fail: tactic `stepping` runs no code, so its proof cannot use `step`
```
