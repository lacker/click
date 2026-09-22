# Final parent detach must account for the conditional child release

```c filename=shared_heap_final_detach.c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release(kid);
    p->kid = 0;
}

void caller(struct parent* p, struct child* kid) {
    parent_detach(p);
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
        ParentLink::Empty => {
            owns &p->kid;
            fact p->kid == 0;
        },
        ParentLink::Linked(kid) => {
            owns &p->kid;
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

verifying "shared_heap_final_detach.c";

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_ref(obj);
} by {
    if obj->refs == 1 {
        unfold(child_ref(obj));
        execute();
        simp();
    } else {
        open(child_ref(obj)) {
            execute();
        }
        have 1 < old(obj->refs) by {
            arithmetic() using {
                1 <= old(obj->refs);
                old(obj->refs) != 1;
            }
        }
        have old(obj->refs) - 1 >= 1 by {
            apply(int32_above_one_predecessor_is_at_least_one(old(obj->refs))) using {
                1 < old(obj->refs);
            }
        }
        have old(obj->refs) == old(count(child_ref(obj))) by { simp(); }
        have old(count(child_ref(obj))) > 1 by {
            simp() using {
                old(obj->refs) > 1;
                old(obj->refs) == old(count(child_ref(obj)));
            }
        }
        have count(child_ref(obj)) != 0 by {
            arithmetic() using { old(count(child_ref(obj))) > 1; }
        }
        simp();
    }
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    consumes child_ref(p->kid);
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
    consumes &p->kid;
    requires kid != 0;
    requires p->kid == kid;
    requires kid->refs == 1;
    consumes child_ref(kid);
} by {
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    let out = step(parent_detach(p), { link: link });
    step();
    simp();
}
```

```expect
pass
```
