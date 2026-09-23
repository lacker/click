# An owned heap parent carries one counted child reference

This focused heap-parent regression uses the ordinary branch-on-count child
release. The parent link is folded across modular calls. Detach resolves
`child_ref(p->kid)` from the exact owned parent instance and then consumes
the actual child reference. The null allocation path releases the creator
reference. The frozen two-parent C source remains in
`design/shared-heap-probes/shared_parent.c`.

```c filename=shared_heap_one_heap_parent.c
struct child { int32 refs; int32 payload; };
struct parent { struct child* kid; };
void child_retain(struct child* obj) { obj->refs = obj->refs + 1; }
void child_release(struct child* obj) {
    if (obj->refs == 1) { free(obj); }
    else { obj->refs = obj->refs - 1; }
}
void parent_attach(struct parent* p, struct child* kid) {
    p->kid = kid;
    child_retain(kid);
}
void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release(kid);
    free(p);
}
int32 caller(struct child* kid) {
    struct parent* p = malloc(sizeof(struct parent));
    if (p == 0) {
        child_release(kid);
        return -1;
    }
    parent_attach(p, kid);
    child_release(kid);
    parent_detach(p);
    return 0;
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

resource child_ref(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    fact obj->refs == count(child_ref(obj));
}

verifying "shared_heap_one_heap_parent.c";

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
    requires 1 <= obj->refs;
    consumes child_ref(obj);
    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;
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

void parent_attach(struct parent* p, struct child* kid) {
    requires count(child_ref(kid)) < 2147483647;
    requires kid != 0;
    consumes &p->kid;
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
    consumes child_ref(p->kid);
    consumes allocation(p, sizeof(struct parent));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            have old(p->kid) == kid by simp;
            execute();
            simp();
        },
    }
}

int32 caller(struct child* kid) {
    requires kid != 0;
    requires count(child_ref(kid)) == 1;
    consumes child_ref(kid);
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch {
        then {
            step(child_release(kid), {});
            step();
            simp();
        }
        else {}
    }
    let { link: link } = step(parent_attach(p, kid), {});
    step(child_release(kid), {});
    step(parent_detach(p), { link: link });
    step();
    simp();
}

```

```expect
pass
```
