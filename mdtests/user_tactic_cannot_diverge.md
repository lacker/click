# a tactic cannot declare `diverges`

A tactic is applied as a proved rule. One that need not terminate could
justify anything, so a tactic signature may not declare `diverges`.

```c filename=user_tactic_cannot_diverge.c
struct pr { int32 a; int32 b; };

void user(struct pr *p) {
}
```

```click
verifying "user_tactic_cannot_diverge.c";

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


tactic forever(p: struct pr*) diverges {
    owns x: both(p);
} by {
    have 1 == 1;
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
fail: a tactic runs no code, so its signature cannot declare `diverges`
```
