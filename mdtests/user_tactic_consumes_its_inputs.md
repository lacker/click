# an instance a tactic consumes is gone after the application

`divide` consumes `x`. After the application the proof holds `y` and `z`, and
`x` no longer names an instance, so unfolding it is refused.

```c filename=user_tactic_consumes_its_inputs.c
struct pr { int32 a; int32 b; };

void user(struct pr *p) {
}
```

```click
verifying "user_tactic_consumes_its_inputs.c";

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
    ensures y.tag == 7;
} by {
    unfold(x);
    let y = fold(first(p), { tag: 7 });
    let z = fold(second(p), { tag: 0 });
    have y.tag == 7;
}

void user(struct pr* p) {
    consumes x: both(p);
} by {
    let { y: y, z: z } = divide(p, { x: x });
    unfold(x);
    step();
    step();
    close();
}
```

```expect
fail: resource instance is not owned
```
