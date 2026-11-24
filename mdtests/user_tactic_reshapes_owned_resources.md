# a user-defined tactic reshapes the resources a proof holds

`divide` is a user-defined tactic. Its contract consumes one instance owning
`p->a` and `p->b` and produces two, one per cell, with a fact about the first.
Its `by` block proves that contract once, by unfolding and folding; no C runs.

`user` applies it as one step, `let { y: y, z: z } = divide(p, { x: x });`, which
binds `divide`'s `x` to the instance `user` holds and names the two it gets
back. An application changes only which instances the proof holds and adds the
tactic's `ensures`; memory is untouched, so the requirement `p->b == 5` still
holds afterwards and proves the result.

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
    let { y: y, z: z } = divide(p, { x: x });
    unfold(z);
    step();
    let z = fold(second(p), { tag: 0 });
    close();
}
```

```expect
pass
```
