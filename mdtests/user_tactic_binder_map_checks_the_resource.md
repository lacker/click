# a tactic's binder map checks the resource each binder expects

`divide`'s `x` expects a `both` instance. Binding it to `z`, a `second`
instance, is refused where it is written, as a call step's map is.

```c filename=user_tactic_binder_map_checks_the_resource.c
struct pr { int32 a; int32 b; };

void user(struct pr *p) {
}
```

```click
verifying "user_tactic_binder_map_checks_the_resource.c";

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
    consumes z: second(p);
} by {
    let { y: y, z: z2 } = divide(p, { x: z });
    step();
    step();
    close();
}
```

```expect
fail: binder `x` expects resource `both`, but `z` is `second`
```
