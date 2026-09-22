# Entry-state resource arguments remain valid at function exit

```c filename=shared_heap_detach_old_resource_handoff.c
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
            owns &p->kid;
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

verifying "shared_heap_detach_old_resource_handoff.c";

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
```

```expect
pass
```
