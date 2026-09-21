# Produced resource ensures transport their model fields across a call

The constructor fact in a callee's `ensures` clause must be available on the
caller-side produced resource. The second call should be able to use that fact
to select the matched resource arm without restating it with `have`.

```c filename=shared_heap_produced_ensure_transport.c
struct child {
    int32 value;
};

struct parent {
    struct child* kid;
};

void parent_attach(struct parent* p, struct child* kid) {
    p->kid = kid;
}

void parent_detach(struct parent* p) {
    p->kid = 0;
}

void caller(struct parent* p, struct child* kid) {
    parent_attach(p, kid);
    parent_detach(p);
}
```

```click
spec enum ParentLink {
    Empty,
    Linked(struct child*),
}

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {},
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

verifying "shared_heap_produced_ensure_transport.c";

void parent_attach(struct parent* p, struct child* kid) {
    consumes p->kid;
    requires kid != 0;
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
} by {
    execute();
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    simp();
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            execute();
            simp();
        },
    }
}

void caller(struct parent* p, struct child* kid) {
    consumes p->kid;
    requires kid != 0;
} by {
    let link = step(parent_attach(p, kid), {});
    step(parent_detach(p), { link: link });
    step();
    simp();
}
```

```expect
pass
```
