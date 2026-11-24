# A parent detach consumes one reference from the shared population

The creator releases its reference before either parent detaches. After the
first detach, one reference remains. The proof below deliberately asserts
that two remain; it must fail at that false count claim. Previously it failed
earlier while transporting the child invariant through `parent_detach`.

The caller starts with the creator's one reference. Its explicit population
precondition records that total; borrowing control alone permits an arbitrary
entry population.

```c filename=shared_heap_two_parent_branch_release.c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

void child_retain(struct child* obj) {
    obj->refs = obj->refs + 1;
}

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

void parent_attach(struct parent* p, struct child* kid) {
    p->kid = kid;
    child_retain(kid);
}

int32 parent_read_payload(struct parent* p) {
    struct child* kid = p->kid;
    return kid->payload;
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release(kid);
    p->kid = 0;
}

void caller(struct parent* first, struct parent* second, struct child* kid) {
    parent_attach(first, kid);
    parent_attach(second, kid);
    child_release(kid);
    parent_detach(first);
    int32 observed = parent_read_payload(second);
    parent_detach(second);
}
```

```click
import click::integer;

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

authorized resource child_ref(obj: struct child*) {}

function child_object(obj: struct child*) -> Bool { true }

resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact to_integer(obj->refs) == to_integer(count(child_ref(obj)));
}

verifying "shared_heap_two_parent_branch_release.c";

void child_retain(struct child* obj) {
    requires to_integer(count(child_ref(obj))) < 2147483647;
    owns child_control(obj);
    produces child_ref(obj);
} by {
    unfold(child_control(obj));
    step();
    fold(child_ref(obj));
    fold(child_control(obj));
}

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(obj->refs) > 1 { produces child_control(obj); }
    ensures to_integer(count(child_ref(obj))) == to_integer(old(count(child_ref(obj))) - 1);
} by {
    unfold(child_control(obj));
    if obj->refs == 1 {
        unfold(child_ref(obj));
        unfold(authority(child_ref(obj)));
        step_until(function.exit);
        close();
    } else {
        unfold(child_ref(obj));
        have 1 < obj->refs by {
            close() using { 1 <= obj->refs; obj->refs != 1; };
        }
        have to_integer(obj->refs - 1) >= 1;
        step();
        step();
        fold(child_control(obj));
        step_until(function.exit);
        close();
    }
}

void parent_attach(struct parent* p, struct child* kid) {
    requires to_integer(count(child_ref(kid))) < 2147483647;
    requires kid != 0;
    consumes p->kid;
    owns child_control(kid);
    owns child_ref(kid);
    produces child_ref(kid);
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
} by {
    step();
    step();
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
}

int32 parent_read_payload(struct parent* p) {
    owns link: parent(p);
    requires link.link != ParentLink::Empty;
    owns child_control(p->kid);
    owns child_ref(p->kid);
    ensures result == p->kid->payload;
    ensures result == old(p->kid->payload);
    ensures p->kid == old(p->kid);
    ensures link.link == ParentLink::Linked(old(p->kid));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(entry_child) => {
            unfold(link);
            with(child_control(p->kid)) { step_until(function.exit); }
            let link = fold(parent(p), { link: ParentLink::Linked(p->kid) });
            close();
        },
    }
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    consumes child_control(p->kid);
    if old(p->kid->refs) > 1 { produces child_control(old(p->kid)); }
    consumes child_ref(p->kid);
    produces out: parent(old(p));
    ensures old(p->kid->refs) > 1 implies
        to_integer(old(p->kid)->refs) == to_integer(old(p->kid->refs)) - 1;
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(entry_child) => {
            unfold(link);
            have old(p->kid) == entry_child by close();
            if p->kid->refs > 1 {
                have to_integer(old(p->kid->refs)) == to_integer(old(count(child_ref(p->kid)))) by close();
                step_until(statement(1).entry);
                step(child_release);
                with(child_control(kid)) {
                    have to_integer(kid->refs) == to_integer(old(p->kid->refs)) - 1 by {
                        rewrite(to_integer(kid->refs), to_integer(count(child_ref(kid))));
                        close();
                    }
                    have separate(memory(kid->refs), memory(p->kid)) by close();
                }
                mark before_clear;
                step();
                have separate(statement(2).footprint, memory(kid->refs)) by {
                    normalize() using { at(before_clear, separate(memory(kid->refs), memory(p->kid))); };
                }
                have kid->refs == at(before_clear, kid->refs) by { preserve(memory(kid->refs), statement(2)); }
                have to_integer(old(p->kid)->refs) == to_integer(old(p->kid->refs)) - 1 by {
                    rewrite(old(p->kid), kid);
                    rewrite(kid->refs, at(before_clear, kid->refs));
                    close();
                }
                let out = fold(parent(p), { link: ParentLink::Empty });
                step_until(function.exit);
                close();
            } else {
                step_until(function.exit);
                let out = fold(parent(p), { link: ParentLink::Empty });
                close();
            }
        },
    }
}

void caller(struct parent* first, struct parent* second, struct child* kid) {
    requires child_object(kid);
    consumes first->kid;
    consumes second->kid;
    requires kid != 0;
    requires to_integer(count(child_ref(kid))) == 1;
    owns child_control(kid);
    owns child_ref(kid);
} by {
    let { link: first_link } = step(parent_attach);
    have to_integer(count(child_ref(kid))) == 2 by close();
    let { link: second_link } = step(parent_attach);
    have count(child_ref(kid)) == 3 by close();
    step(child_release);
    have to_integer(count(child_ref(kid))) == 2 by close();
    unfold(first_link);
    have first->kid == kid by close();
    with(child_control(kid)) {
        have kid->refs > 1 by close();
        have first->kid->refs > 1 by { rewrite(first->kid, kid); close(); }
    }
    let first_link = fold(parent(first), { link: ParentLink::Linked(kid) });
    let { out: first_out } = step(parent_detach, { link: first_link });
    step();
    with(child_control(kid)) {
        have count(child_ref(kid)) == 1 by close();
    }
    have count(child_ref(kid)) == 2 by close();
    step(parent_read_payload, { link: second_link });
    let { out: second_out } = step(parent_detach, { link: second_link });
    step();
    close();
}
```

```expect
fail: could not establish `to_integer(count(child_ref(kid))) == 2`
```
