# A fold over a hidden record still checks the parent's facts

`clear` unfolds `pair`, stores `-1` to `p->n`, and folds `pair` back from
the unchanged child. The fact `p->n == first.v` no longer holds: `first.v`
is the child's field, which is not negative, and the cell now is. The fold
is refused.

The fold that holds is `a_resource_without_fields_names_a_child_with_fields.md`.

```c filename=a_fold_over_a_hidden_record_still_checks_the_facts.c
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

verifying "a_fold_over_a_hidden_record_still_checks_the_facts.c";

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
