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

verifying "shared_parent.c";

void child_init(struct child* obj, int32 payload) {
    consumes allocation(obj, sizeof(struct child));
    consumes object(obj);
    produces child_ref(obj);
    ensures obj->payload == payload;
} by {
    execute();
    fold(child_ref(obj));
    simp();
}

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

int32 parent_read_payload(struct parent* p) {
    owns link: parent(p);
    requires link.link != ParentLink::Empty;
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
        ParentLink::Linked(kid) => {
            unfold(link);
            open(child_ref(p->kid)) { execute(); }
            let link = fold(parent(p), { link: ParentLink::Linked(p->kid) });
            simp();
        },
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
            have old(p->kid) == kid by simp;
            execute();
            let out = fold(parent(p), { link: ParentLink::Empty });
            simp();
        },
    }
}
