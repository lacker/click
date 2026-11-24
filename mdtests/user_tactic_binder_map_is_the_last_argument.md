# a tactic's binder map is its last argument

A tactic application writes its binder map inside the parentheses, as a call
step and a fold write theirs: `divide(p, { x: x })`. A brace block after a
call is a proof block everywhere else in Click, so the trailing form is
refused with the spelling to write.

```c filename=user_tactic_reshapes_owned_resources.c
struct pr { int32 a; int32 b; };

int32 user(struct pr *p) {
    return p->b;
}
```

```click
verifying "user_tactic_reshapes_owned_resources.c";

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

int32 user(struct pr* p) {
    consumes x: both(p);
    requires p->b == 5;
    produces y: first(p);
    produces z: second(p);
    ensures result == 5;
    ensures y.tag == 7;
} by {
    let { y: y, z: z } = divide(p) { x: x };
    unfold(z);
    step();
    let z = fold(second(p), { tag: 0 });
    close();
}
```

```expect
fail: the binder map is the last argument of a tactic application: write `divide(..., { binder: instance })`
```
