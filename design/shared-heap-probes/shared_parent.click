spec enum ParentLink {
    Empty,
    Linked(struct child*),
}

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {
            owns &p->kid;
            fact defined(p->kid);
            fact p->kid == 0;
        },
        ParentLink::Linked(kid) => {
            owns &p->kid;
            fact defined(p->kid);
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

resource child_ref(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    fact defined(obj->refs);
    fact defined(obj->payload);
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
    ensures obj->payload == old(obj->payload);
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
    ensures old(count(child_ref(obj))) > 1 implies obj->payload == old(obj->payload);
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
    requires separate(memory(&p->kid), memory(kid->payload));
    consumes &p->kid;
    owns child_ref(kid);
    produces child_ref(kid);
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
    ensures p->kid == kid;
    ensures kid->payload == old(kid->payload);
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
    ensures link.link == old(link.link);
    ensures link.link == ParentLink::Linked(old(p->kid));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            have old(p->kid) == kid by { simp(); }
            open(child_ref(p->kid)) { execute(); }
            let link = fold(parent(p), { link: ParentLink::Linked(kid) });
            simp();
        },
    }
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    consumes child_ref(p->kid);
    produces &p->kid;
    ensures old(count(child_ref(p->kid))) > 1 implies old(p->kid)->payload == old(p->kid->payload);
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

int32 run_first_destroyed(int32 payload) {
    ensures result == -1 or result == payload;
} by {
    step();
    step();
    branch { then { step(); simp(); } else {} }
    step();
    step();
    step();
    branch { then { step(); step(); simp(); } else {} }
    step();
    step();
    branch { then { step(); step(); step(); simp(); } else {} }
    let { link: first_link } = step(parent_attach(first, kid), {});
    let { link: second_link } = step(parent_attach(second, kid), {});
    step(child_release(kid), {});
    have first->kid == kid by { simp(); }
    have kid->payload == payload by { simp(); }
    have count(child_ref(first->kid)) > 1 by { simp(); }
    have first->kid->payload == payload by { rewrite(first->kid == kid); simp(); }
    mark detaching;
    step(parent_detach(first), { link: first_link });
    have at(detaching, first->kid) == kid by { assumption(); }
    have at(detaching, first->kid)->payload == at(detaching, first->kid->payload) by { simp(); }
    have at(detaching, first->kid->payload) == payload by { assumption(); }
    have at(detaching, first->kid)->payload == payload by {
        simp() using {
            at(detaching, first->kid)->payload == at(detaching, first->kid->payload);
            at(detaching, first->kid->payload) == payload;
        }
    }
    have kid->payload == payload by {
        have kid == at(detaching, first->kid) by { simp() using { at(detaching, first->kid) == kid; } }
        rewrite(kid == at(detaching, first->kid));
        assumption();
    }
    step();
    have second->kid == kid by { simp(); }
    have second->kid->payload == payload by { rewrite(second->kid == kid); simp(); }
    mark reading;
    step(parent_read_payload(second), { link: second_link });
    have at(reading, second->kid->payload) == payload by { assumption(); }
    have out == at(reading, second->kid->payload) by { simp(); }
    have out == payload by { simp(); }
    step(parent_detach(second), { link: second_link });
    step();
    step();
    step();
    simp();
}

int32 run_second_destroyed(int32 payload) {
    ensures result == -1 or result == payload;
} by {
    step();
    step();
    branch { then { step(); simp(); } else {} }
    step();
    step();
    step();
    branch { then { step(); step(); simp(); } else {} }
    step();
    step();
    branch { then { step(); step(); step(); simp(); } else {} }
    let { link: first_link } = step(parent_attach(first, kid), {});
    let { link: second_link } = step(parent_attach(second, kid), {});
    step(child_release(kid), {});
    have second->kid == kid by { simp(); }
    have kid->payload == payload by { simp(); }
    have count(child_ref(second->kid)) > 1 by { simp(); }
    have second->kid->payload == payload by { rewrite(second->kid == kid); simp(); }
    mark detaching;
    step(parent_detach(second), { link: second_link });
    have at(detaching, second->kid) == kid by { assumption(); }
    have at(detaching, second->kid)->payload == at(detaching, second->kid->payload) by { simp(); }
    have at(detaching, second->kid->payload) == payload by { assumption(); }
    have at(detaching, second->kid)->payload == payload by {
        simp() using {
            at(detaching, second->kid)->payload == at(detaching, second->kid->payload);
            at(detaching, second->kid->payload) == payload;
        }
    }
    have kid->payload == payload by {
        have kid == at(detaching, second->kid) by { simp() using { at(detaching, second->kid) == kid; } }
        rewrite(kid == at(detaching, second->kid));
        assumption();
    }
    step();
    have first->kid == kid by { simp(); }
    have first->kid->payload == payload by { rewrite(first->kid == kid); simp(); }
    mark reading;
    step(parent_read_payload(first), { link: first_link });
    have at(reading, first->kid->payload) == payload by { assumption(); }
    have out == at(reading, first->kid->payload) by { simp(); }
    have out == payload by { simp(); }
    step(parent_detach(first), { link: first_link });
    step();
    step();
    step();
    simp();
}
