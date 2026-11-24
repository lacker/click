# An unproved tactic requirement refuses the application

`check_first` requires `p->a == 1`. The implicit closer cannot establish that
requirement in this caller, so the application is refused.

```c filename=user_tactic_application_owes_its_requirements.c
struct pr { int32 a; int32 b; };

void user(struct pr *p) {
}
```

```click
verifying "user_tactic_application_owes_its_requirements.c";

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


tactic check_first(p: struct pr*) {
    owns x: both(p);
    requires p->a == 1;
    ensures 1 == 1;
} by {
    have 1 == 1;
}

void user(struct pr* p) {
    owns x: both(p);
} by {
    check_first(p, { x: x });
    step();
    step();
    close();
}
```

```expect
fail: tactic `check_first` requires
```
