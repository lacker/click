# a tactic cannot take the name of a built-in tactic

`rewrite` is a built-in tactic, so a user-defined tactic of that name would make
`rewrite(...)` mean two things in a proof. It is refused where it is declared.

```c filename=user_tactic_cannot_shadow_a_builtin.c
struct pr { int32 a; int32 b; };

void user(struct pr *p) {
}
```

```click
verifying "user_tactic_cannot_shadow_a_builtin.c";

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

tactic rewrite(p: struct pr*) {
    consumes x: both(p);
    produces y: first(p);
    produces z: second(p);
    ensures y.tag == 7;
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
fail: tactic `rewrite` would shadow the built-in tactic of the same name
```
