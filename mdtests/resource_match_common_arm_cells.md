# A requirement reads what the possible arms agree on

A requirement that refutes one arm of a three-constructor model does not select
an arm: two are left, and neither is decided. The two that are left can still
agree about a cell. `requires c.model != Shape::Top` rules out the only arm that
owns nothing, and both `Shape::Left` and `Shape::Right` own `p->value`, so
`requires p->value >= 0` reads it — through the folded instance, as a view, with
ownership untouched.

This is decision D7 extended from the arm the premises select to the arms they
leave possible: what is published is the intersection of those arms' own memory
clauses, computed once per arm. `p->tag` would not be published, because only
`Shape::Left` owns it — a cell the possible arms disagree about is still
refused, which is
[`resource_match_arm_needs_one_entailed_arm.md`](resource_match_arm_needs_one_entailed_arm.md).

The body's own read is a different question. Executing `return p->value;` needs
the cell to be owned, so the proof still names the constructor: a `match` on the
model closes the refuted arm by contradiction and unfolds the other two.

```c filename=commonarm.c
struct cell { int32 tag; int32 value; };
int32 read_value(struct cell *p) { return p->value; }
```

```click
verifying "commonarm.c";

spec enum Shape { Top, Left(int32), Right(int32) }

resource cell_at(p: struct cell*) {
    field model: Shape;
    match model {
        Shape::Top => { fact p == 0; },
        Shape::Left(value) => {
            owns p->tag;
            owns p->value;
            fact p != 0;
            fact p->value == value;
        },
        Shape::Right(value) => {
            owns p->value;
            fact p != 0;
            fact p->value == value;
        },
    }
}

int32 read_value(struct cell* p) {
    owns c: cell_at(p);
    requires c.model != Shape::Top;
    requires p->value >= 0;
    ensures result >= 0;
} by {
    match c.model {
        Shape::Top => { contradiction(c.model == Shape::Top); },
        Shape::Left(value) => {
            unfold(c);
            execute();
            let c = fold(cell_at(p), { model: Shape::Left(value) });
            simp();
        },
        Shape::Right(value) => {
            unfold(c);
            execute();
            let c = fold(cell_at(p), { model: Shape::Right(value) });
            simp();
        },
    }
}
```

```expect
pass
```
