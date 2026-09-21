# A produced parent link carries its child-resource argument through a call

The parent link produced by `parent_attach` records that `p->kid == kid`.
`parent_detach` should be able to use that fact when requesting the counted
child resource through the field spelling `child_ref(p->kid)`.

```c filename=shared_heap_composed_attach_detach.c
struct child {
    int32 refs;
};

struct parent {
    struct child* kid;
};

void child_retain(struct child* obj) {
    obj->refs = obj->refs + 1;
}

void child_release(struct child* obj) {
    obj->refs = obj->refs - 1;
}

void parent_attach(struct parent* p, struct child* kid) {
    p->kid = kid;
    child_retain(kid);
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release(kid);
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

resource child_ref(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    fact obj->refs == count(child_ref(obj));
}

verifying "shared_heap_composed_attach_detach.c";

void child_retain(struct child* obj) {
    requires count(child_ref(obj)) < 2147483647;
    owns child_ref(obj);
    produces child_ref(obj);
} by {
    open(child_ref(obj)) {
        execute();
    }
    simp();
}

void child_release(struct child* obj) {
    requires 1 < count(child_ref(obj));
    owns child_ref(obj);
    consumes child_ref(obj);
} by {
    open(child_ref(obj)) {
        have 1 < obj->refs by simp;
        have obj->refs - 1 >= 1 by {
            apply(int32_above_one_predecessor_is_at_least_one(obj->refs)) using {
                1 < obj->refs;
            }
        }
        execute();
    }
    simp();
}

void parent_attach(struct parent* p, struct child* kid) {
    requires count(child_ref(kid)) < 2147483647;
    requires kid != 0;
    consumes p->kid;
    owns child_ref(kid);
    produces child_ref(kid);
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
    owns child_ref(p->kid);
    consumes child_ref(p->kid);
    produces child_ref(old(p->kid));
    produces out: parent(old(p));
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

void caller(struct parent* p, struct child* kid) {
    consumes p->kid;
    requires kid != 0;
    owns child_ref(kid);
} by {
    let { link: link } = step(parent_attach(p, kid), {});
    let out = step(parent_detach(p), { link: link });
    step();
    simp();
}
```

```expect
pass
```
