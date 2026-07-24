theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        simp();
    }
}

resource empty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact owner->len == 0;
    fact 1 <= owner->cap;
    fact separate(memory(owner[0..4]), memory((owner->data)[0..owner->cap]));
}

resource nonempty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(owner[0..4]), memory((owner->data)[0..owner->cap]));
}

verifying "vector_init.c";
verifying "vector_len.c";
verifying "vector_get.c";
verifying "vector_set.c";
verifying "vector_fill.c";
verifying "vector_replace_if.c";
verifying "vector_push_first.c";
verifying "vector_clear.c";
verifying "vector_pipeline.c";

int32 vector_init(struct vector* owner, int32 data[], int32 capacity) {
    requires 1 <= capacity;
    consumes owner[0..4];
    consumes data[0..capacity];
    mutable_field(owner->len), (owner->cap), (owner->data);
    produces empty_vector(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->cap == capacity;
    ensures owner->data == data;
} by {
    execute_rest();
    fold(empty_vector(owner));
    frame();
    simp();
}

int32 vector_len(struct vector* owner) {
    views nonempty_vector(owner);
    immutable;

    ensures result == owner->len by auto;
}

int32 vector_get(struct vector* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views nonempty_vector(owner);
    immutable;

    ensures result == (owner->data)[index];
    ensures result == old((owner->data)[index]);
} by {
    execute_rest();
    frame();
    simp();
}

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;
    mutable (owner->data)[index..index + 1];
    owns nonempty_vector(owner);
    ensures result == value;
    ensures (owner->data)[index] == value;
    ensures owner->len == old(owner->len);
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    unfold(nonempty_vector(owner));
    execute_step();
    execute_step();
    execute_step();
    step using {
        fact 0 <= index;
        fact index < load_int32(owner);
        fact loadable(old(owner[0..1]));
        fact loadable(old((owner + 1)[0..1]));
        fact loadable(old((owner + 2)[0..2]));
        fact 1 <= load_int32(owner);
        fact load_int32(owner) <= load_int32((owner + 1));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
    }
    fold(nonempty_vector(owner));
    have index < index + 1 by { simp(); }
    frame();
    simp();
}

int32 vector_fill(struct vector* owner, int32 value) {
    owns nonempty_vector(owner);
    mutable (owner->data)[0..owner->len];

    for loop(0) as fill_cells {
        invariant i >= 0 and i <= owner->len;
        invariant forall (int32 k) {
            0 <= k and k < i implies (owner->data)[k] == value
        };
        mutable (owner->data)[0..owner->len] by frame;
        initialize by simp;
        preserve by {
            unfold(nonempty_vector(owner));
            have i < owner->cap by simp;
            execute_step();
            execute_step();
            simp();
        }
    }

    ensures result == owner->len;
    ensures forall (int32 k) {
        0 <= k and k < owner->len implies (owner->data)[k] == value
    };
} by {
    execute_rest();
    frame();
    simp();
}

int32 vector_replace_if(
    struct vector* owner,
    int32 index,
    int32 replacement,
    int32 replace
) {
    requires 0 <= index;
    requires index < owner->len;
    owns nonempty_vector(owner);
    mutable (owner->data)[index..index + 1];

    for statement(3) as choose_replacement {
        assert replace == replace by auto;
    }

    ensures replace != 0 implies result == replacement;
} by {
    execute_step();
    execute_step();
    step using {
        fact index < load_int32(owner);
        fact 0 <= index;
        fact 1 <= *owner;
        fact *owner <= *(owner + 1);
        fact loadable(old((owner + 1)[0..1]));
        fact loadable(old((owner + 2)[0..2]));
        fact loadable(old(owner[0..1]));
    }
    advance(choose_replacement.exit)
    ensuring {
        fact replace != 0 implies selected == replacement;
        fact not (replace != 0) implies selected == original;
        fact index < index + 1;
        owns nonempty_vector(owner);
    }
    by {
        if replace != 0 {
            execute_then_step();
            step using {
                fact index < load_int32(owner);
                fact 0 <= index;
                fact 1 <= *owner;
                fact *owner <= *(owner + 1);
                fact replace != 0;
                fact original == *(owner + 1);
                fact loadable(old((owner + 1)[0..1]));
                fact loadable(old((owner + 2)[0..2]));
                fact loadable(old(owner[0..1]));
            }
            have replace != 0 implies selected == replacement by simp;
            have not (replace != 0) implies selected == original by simp;
            have index < index + 1 by simp;
        } else {
            execute_else_step();
            execute_step();
            have replace != 0 implies selected == replacement by simp;
            have not (replace != 0) implies selected == original by simp;
            have index < index + 1 by simp;
        }
    }
    execute_rest();
    have index < index + 1 by { simp(); }
    frame();
    simp();
}

int32 vector_push_first(struct vector* owner, int32 value) {
    consumes empty_vector(owner);
    mutable owner[0..1], (owner->data)[0..1];
    produces nonempty_vector(owner);
    ensures result == 1;
    ensures owner->len == 1;
    ensures (owner->data)[0] == value;
} by {
    unfold(empty_vector(owner));
    have owner->len < owner->cap by simp;
    have 0 <= owner->len by simp;
    have owner->len < 1 by simp;
    execute_until(statement(8));
    have owner->len == 1 by simp;
    have 1 <= owner->len by simp;
    have owner->len <= owner->cap by simp;
    have separate(memory(owner[0..4]), memory((owner->data)[0..owner->cap])) by {
        simp();
    }
    fold(nonempty_vector(owner));
    execute_rest();
    frame();
    simp();
}

int32 vector_clear(struct vector* owner) {
    consumes nonempty_vector(owner);
    mutable_field(owner->len);
    produces empty_vector(owner);
    ensures result == 0;
    ensures owner->len == 0;
} by {
    unfold(nonempty_vector(owner));
    execute_rest();
    have owner->len == 0 by simp;
    have 1 <= owner->cap by simp;
    have separate(memory(owner[0..4]), memory((owner->data)[0..owner->cap])) by {
        simp();
    }
    fold(empty_vector(owner));
    frame();
    simp();
}

int32 vector_pipeline(
    struct vector* owner,
    int32 data[],
    int32 capacity,
    int32 first,
    int32 replacement
) {
    requires 1 <= capacity;
    consumes owner[0..4];
    consumes data[0..capacity];

    for statement(6) as read_replacement {
        assert owner->len == 1 by auto;
    }

    produces empty_vector(owner);
    ensures result == replacement;
} by {
    execute_until(statement(3));
    have owner->len == 0 by {
        simp();
    }
    have owner->cap == capacity by {
        simp();
    }
    execute_until(statement(4));
    have owner->len == 1 by {
        simp();
    }
    have 0 < owner->len by {
        simp();
    }
    execute_until(statement(5));
    have owner->len == 1 by {
        simp();
    }
    have 0 < owner->len by {
        simp();
    }
    execute_until(read_replacement);
    have at(statement(5).entry, owner->len) == 1 by {
        simp();
    }
    have owner->len == at(statement(5).entry, owner->len) by {
        simp();
    }
    apply(int32_equality_transitive(
        owner->len,
        at(statement(5).entry, owner->len),
        1
    ));
    have owner->len == 1 by {
        simp();
    }
    observe(nonempty_vector(owner));
    have (owner->data)[0] == replacement by {
        simp();
    }
    execute_until(statement(7));
    have observed == at(statement(6).entry, (owner->data)[0]) by {
        simp();
    }
    have at(statement(6).entry, (owner->data)[0]) == replacement by {
        simp();
    }
    apply(int32_equality_transitive(
        observed,
        at(statement(6).entry, (owner->data)[0]),
        replacement
    ));
    have observed == replacement by {
        simp();
    }
    execute_rest();
    simp();
}
