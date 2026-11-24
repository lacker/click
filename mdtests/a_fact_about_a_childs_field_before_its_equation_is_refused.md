# A fact about a child's field before its equation is refused

The equation `fact first.v == first_v;` says where the child's field is
kept, and a later `first.v` reads that parent field. Here the fact that
uses `first.v` is written first, where nothing yet says which parent field
it is, so it is taken as an equation for the child's field itself and the
real one is a second.

```c filename=a_fact_about_a_childs_field_before_its_equation_is_refused.c
struct cell { int32 value; };
struct pair { struct cell* a; int32 n; };

int32 get(struct pair* p) {
    return p->n;
}

void set(struct pair* p) {
    p->n = p->a->value;
}
```

```click
resource counted(c: struct cell*) {
    field v: int32;
    owns c->value;
    fact c->value == v;
}

resource pair(p: struct pair*) {
    field first_v: int32;
    owns p->a;
    owns p->n;
    owns first: counted(p->a);
    fact p->n == first.v;
    fact first.v == first_v;
}

verifying "a_fact_about_a_childs_field_before_its_equation_is_refused.c";

int32 get(struct pair* p) {
    owns x: pair(p);
    ensures result == x.first_v;
} by {
    let { first: c, first_v: v } = unfold(x);
    step_until(function.exit);
    let x = fold(pair(p), { first_v: v, first: c });
    close();
}
```

```expect
fail: write `fact first.v == parent_field;` before any other fact that reads `first.v`
```
