# A refused fold shows the hidden record it proposed

`clear` stores `-1` into `p->n`, so refolding `pair(p)` from the child `c`
fails at the body fact `p->n == first.v`. The generated obligation names the
selected child directly as `p->n == c.v`, exposing the value the proposed
hidden record would use.

```c filename=a_refused_fold_shows_the_hidden_record_it_proposed.c
struct cell { int32 value; };
struct pair { struct cell* a; int32 n; };

void clear(struct pair* p) {
    p->n = -1;
}
```

```click
resource counted(c: struct cell*) {
    field v: int32;
    owns c->value;
    fact c->value == v;
}

resource pair(p: struct pair*) {
    owns p->a;
    owns p->n;
    owns first: counted(p->a);
    fact p->n == first.v;
    fact first.v >= 0;
}

verifying "a_refused_fold_shows_the_hidden_record_it_proposed.c";

void clear(struct pair* p) {
    owns x: pair(p);
} by {
    let { first: c } = unfold(x);
    step_until(function.exit);
    let x = fold(pair(p), { first: c });
    close();
}
```

```expect
fail: unproved obligation: `p->n == (c.v as int32)`
```
