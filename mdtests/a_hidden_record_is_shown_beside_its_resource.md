# A hidden record is shown beside its resource in a refusal

`pair` declares no field, so it keeps its child's field `first.v` in a
record the author does not write. A refusal lists the held `pair(p)` with
that record, `record { first.v: old(pair(p).first.v) }`, in the same
spelling as the pure facts, so the reader sees which value the facts
`old(p->n) == old(pair(p).first.v)` and `old(pair(p).first.v) >= 0` are
about. The field's value is the contract's entry model, which `old(..)`
always names. The claim `result >= 1` is false: the record only says the
field is nonnegative.

```c filename=a_hidden_record_is_shown_beside_its_resource.c
struct cell { int32 value; };
struct pair { struct cell* a; int32 n; };

int32 get(struct pair* p) {
    return p->n;
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

verifying "a_hidden_record_is_shown_beside_its_resource.c";

int32 get(struct pair* p) {
    owns pair(p);
    ensures result >= 1;
} by {
    let { first: first } = unfold(pair(p));
    step_until(function.exit);
    fold(pair(p), { first: first });
    close();
}
```

```expect
fail: resource facts: [owns pair(p) record { first.v: old(pair(p).first.v) }
```
