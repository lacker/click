# Leak diagnostics name the declared obligation and its surface pointer

The allocation-lifetime diagnostic should identify the declared resource that
keeps an allocation live. A pointer loaded from a struct field should use the
field's C spelling instead of exposing lowered memory-block and load terms.

```c filename=shared_heap_detach_leak_diagnostic.c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

void child_release_nonfinal(struct child* obj) {
    obj->refs = obj->refs - 1;
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release_nonfinal(kid);
    p->kid = 0;
}
```

```click
spec enum ParentLink {
    Empty,
    Linked(struct child*),
}

resource child_ref(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    fact obj->refs == count(child_ref(obj));
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

verifying "shared_heap_detach_leak_diagnostic.c";

void child_release_nonfinal(struct child* obj) {
    requires 1 < obj->refs;
    owns child_ref(obj);
    consumes child_ref(obj);
} by {
    open(child_ref(obj)) {
        execute();
    }
    simp();
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    owns child_ref(p->kid);
    consumes child_ref(p->kid);
    produces out: parent(p);
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            execute();
            let out = fold(parent(p), { link: ParentLink::Empty });
            simp();
        },
    }
}
```

```expect
fail: live allocation obligation was neither returned nor freed: `owns allocation(p->kid, 8)`; held by owns child_ref(p->kid)
```
