resource nonempty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

verifying "vector_push.c";

int32 vector_push(struct vector* owner, int32 value) {
    requires 0 <= owner->len;
    requires owner->len < owner->cap;
    requires separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
    consumes owner->len;
    consumes owner->cap;
    consumes owner->data;
    consumes owner->data[0..owner->cap];
    mutable owner->len, owner->data[owner->len..owner->len + 1];
    produces nonempty_vector(owner);
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->data[old(owner->len)] == value;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    have owner->len <= owner->len by {
        normalize();
    }
    have owner->len < owner->len + 1 by simp;
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have 1 <= owner->len by {
        simp() using {
            at(statement(5).entry, 0) <= at(statement(5).entry, owner->len);
            at(statement(5).entry, owner->len) < at(statement(5).entry, (owner->len + 1));
        }
    }
    have owner->len <= owner->cap by simp;
    have separate(memory(object(owner)), memory(owner->data[0..owner->cap])) by simp;
    fold(nonempty_vector(owner));
    have at(statement(5).entry, owner->len) <= at(statement(5).entry, owner->len) by {
        normalize();
    }
    have at(statement(5).entry, owner->len) < at(statement(5).entry, (owner->len + 1)) by {
        derive using {
            owner->len < owner->cap;
        }
    }
    have 0 == 0 by {
        normalize();
    }
    frame() using {
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        loadable(owner[0..1]);
        loadable((owner + 1)[0..1]);
        loadable((owner + 2)[0..2]);
        loadable(old(owner->data[0..load_int32(byte_offset(owner, 4))]));
        0 <= owner->len;
        owner->len <= owner->len;
        owner->len < (owner->len + 1);
        owner->len < owner->cap;
        at(statement(5).entry, owner->len) <= at(statement(5).entry, owner->len);
        at(statement(5).entry, owner->len) < at(statement(5).entry, (owner->len + 1));
        0 == 0;
    }
    have result == (old(owner->len) + 1) by {
        normalize();
    }
    have owner->len == (old(owner->len) + 1) by {
        normalize();
    }
    have owner->data[old(owner->len)] == value by {
        normalize();
    }
    have owner->cap == old(owner->cap) by {
        normalize();
    }
    have owner->data == old(owner->data) by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}
