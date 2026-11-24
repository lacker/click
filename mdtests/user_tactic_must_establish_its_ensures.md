# a tactic's proof must establish every `ensures`

`divide` promises `y.tag == 8`, but its proof folds `y` with tag 7. A tactic's
proof ends where its last step leaves it: every produced instance must be held
and every `ensures` an available fact, so the tactic is refused, naming the
claim it did not establish.

```c filename=user_tactic_must_establish_its_ensures.c
struct pr { int32 a; int32 b; };

void user(struct pr *p) {
}
```

```click
verifying "user_tactic_must_establish_its_ensures.c";

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

tactic divide(p: struct pr*) {
    consumes x: both(p);
    produces y: first(p);
    produces z: second(p);
    ensures y.tag == 8;
} by {
    unfold(x);
    let y = fold(first(p), { tag: 7 });
    let z = fold(second(p), { tag: 0 });
    have y.tag == 7;
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
fail: `y.tag == 8`
```
