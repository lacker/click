# Two parent links share one child resource

The caller starts with the creator's one reference. Its explicit population
precondition records that total; borrowing control alone permits an arbitrary
entry population.

Here `child_release` only decrements and requires a total above one, so it
borrows and preserves control. `parent_detach` borrows one surviving reference and consumes one other
reference; the total therefore remains positive, and it returns control
unconditionally through the original child pointer after clearing the parent
field. These contracts preserve the original inputs and strengthen the
resource return guarantee without changing C or the payload claim.

After the release call, `parent_detach` uses the callee's payload guarantee.
It opens the returned control resource to show that clearing the parent link
writes a separate cell, then carries the same payload across that store.

`parent_attach` stores `kid` in its typed model `ParentLink::Linked(kid)`, so
its interface requires `kid`'s original object class to be `struct child`.
A C pointer declaration does not supply that evidence, so `caller` states it
too, with the typed helper `child_object(kid)`, and passes it on.

```c filename=shared_heap_two_parent_caller.c
struct child { int32 refs; int32 payload; };
struct parent { struct child* kid; };

void child_retain(struct child* obj) { obj->refs = obj->refs + 1; }
void child_release(struct child* obj) { obj->refs = obj->refs - 1; }
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
int32 caller(struct parent* first, struct parent* second, struct child* kid) {
    parent_attach(first, kid);
    parent_attach(second, kid);
    parent_detach(first);
    int32 observed = parent_read_payload(second);
    parent_detach(second);
    return observed;
}
```

```click
import click::integer;
import click::separation;

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

verifying "shared_heap_two_parent_caller.c";

void child_retain(struct child* obj) {
    requires to_integer(count(child_ref(obj))) < 2147483647;
    owns child_control(obj);
    produces child_ref(obj);
} by {
    unfold(child_control(obj));
    step();
    fold(child_ref(obj));
    fold(child_control(obj));
    step_until(function.exit);
    close();
}

void child_release(struct child* obj) {
    requires 1 < to_integer(count(child_ref(obj)));
    owns child_control(obj);
    consumes child_ref(obj);
    ensures obj->payload == old(obj->payload);
} by {
    unfold(child_control(obj));
    unfold(child_ref(obj));
    have 1 < obj->refs;
    have to_integer(obj->refs - 1) >= 1;
    step();
    fold(child_control(obj));
    step_until(function.exit);
    close();
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
    step_until(function.exit);
    close();
}

int32 parent_read_payload(struct parent* p) {
    owns link: parent(p);
    requires link.link != ParentLink::Empty;
    owns child_control(p->kid);
    owns child_ref(p->kid);
    ensures result == p->kid->payload;
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
    produces child_control(old(p->kid));
    owns child_ref(p->kid);
    consumes child_ref(p->kid);
    produces out: parent(old(p));
    ensures old(p->kid)->payload == old(p->kid->payload);
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(entry_child) => {
            unfold(link);
            have 2 <= to_integer(old(count(child_ref(p->kid))));
            have to_integer(old(count(child_ref(p->kid)))) > 1 by {
                close() using { 2 <= to_integer(old(count(child_ref(p->kid)))); };
            }
            step();
            step();
            step();
            have old(p->kid) == kid by { close(); }
            have kid->payload == old(p->kid->payload) by { close(); }
            with(child_control(kid)) {
                have separate(memory(p->kid), memory(*kid)) by { close(); }
                have contains(memory(*kid), memory(kid->payload)) by { normalize(); }
                apply(separation::contains_refl(memory(p->kid)));
                apply(separation::separate_restrict(
                    memory(p->kid), memory(*kid), memory(p->kid), memory(kid->payload)));
                mark before_clear;
                step();
                have separate(statement(2).footprint, memory(kid->payload)) by {
                    normalize() using {
                        at(before_clear, separate(memory(p->kid), memory(kid->payload)));
                    };
                }
                have kid->payload == at(before_clear, kid->payload) by {
                    preserve(memory(kid->payload), statement(2));
                }
                have kid->payload == old(p->kid->payload) by {
                    rewrite(kid->payload, at(before_clear, kid->payload));
                    close();
                }
            }
            let out = fold(parent(p), { link: ParentLink::Empty });
            step_until(function.exit);
            close();
        },
    }
}

int32 caller(struct parent* first, struct parent* second, struct child* kid) {
    requires child_object(kid);
    consumes first->kid;
    consumes second->kid;
    requires kid != 0;
    requires to_integer(count(child_ref(kid))) == 1;
    owns child_control(kid);
    owns child_ref(kid);
    ensures result == kid->payload;
} by {
    let { link: first_link } = step(parent_attach);
    let { link: second_link } = step(parent_attach);
    let { out: first_out } = step(parent_detach, { link: first_link });
    step();
    mark before_read;
    step(parent_read_payload, { link: second_link });
    // The read returns a linked parent, which the following detach consumes.
    have second_link.link == ParentLink::Linked(at(before_read, second->kid)) by { close(); }
    have second_link.link != ParentLink::Empty by {
        rewrite(second_link.link, ParentLink::Linked(at(before_read, second->kid)));
        normalize();
    }
    step();
    have second->kid == kid;
    have observed == kid->payload;
    have observed == second->kid->payload by { rewrite(second->kid, kid); close(); }
    mark detaching;
    let { out: second_out } = step(parent_detach, { link: second_link });
    have at(detaching, second->kid) == kid by close();
    have at(detaching, second->kid)->payload == at(detaching, second->kid->payload);
    have observed == at(detaching, second->kid->payload) by close();
    have kid == at(detaching, second->kid) by { close() using { at(detaching, second->kid) == kid; }; }
    have kid->payload == at(detaching, second->kid->payload) by {
        rewrite(kid, at(detaching, second->kid));
        close();
    }
    step();
    close();
}
```

```expect
pass
```
