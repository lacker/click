# chained `a->b->c` field access

This checks that a struct-typed field keeps its struct type, so an arrow
chain through it resolves without an intermediate local. Reading and writing
`o->in->value` both work, and a three-deep chain works too — the contract for
the deep case composes a nested resource rather than spelling a single `owns`
whose base is a doubly-indirect load, which lowering still rejects.

```c filename=chain_get.c
struct inner {
    int32 value;
};

struct outer {
    struct inner* in;
};

int32 chain_get(struct outer* o) {
    return o->in->value;
}
```

```c filename=chain_set.c
struct inner {
    int32 value;
};

struct outer {
    struct inner* in;
};

int32 chain_set(struct outer* o) {
    o->in->value = 5;
    return o->in->value;
}
```

```c filename=deep_get.c
struct leaf {
    int32 value;
};

struct middle {
    struct leaf* leaf;
};

struct root {
    struct middle* mid;
};

int32 deep_get(struct root* r) {
    return r->mid->leaf->value;
}
```

```click
resource inner_cell(o: struct outer*) {
    owns o->in;
    owns (o->in)->value;
}

resource leaf_cell(m: struct middle*) {
    owns m->leaf;
    owns (m->leaf)->value;
}

resource nested(r: struct root*) {
    owns r->mid;
    owns leaf_cell(r->mid);
}

verifying "chain_get.c";
verifying "chain_set.c";
verifying "deep_get.c";

int32 chain_get(struct outer* o) {
    consumes inner_cell(o);
    ensures result == (o->in)->value;
    produces inner_cell(o);
} by {
    unfold(inner_cell(o));
    execute();
    fold(inner_cell(o));
    simp();
}

int32 chain_set(struct outer* o) {
    consumes inner_cell(o);
    ensures result == 5;
    produces inner_cell(o);
} by {
    unfold(inner_cell(o));
    execute();
    fold(inner_cell(o));
    simp();
}

int32 deep_get(struct root* r) {
    consumes nested(r);
    produces nested(r);
} by {
    unfold(nested(r));
    unfold(leaf_cell(r->mid));
    execute();
    fold(leaf_cell(r->mid));
    fold(nested(r));
    simp();
}
```

```expect
pass
```
