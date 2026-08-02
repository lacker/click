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
    fact separate(memory(object(owner)), memory((owner->data)[0..owner->cap]));
}

resource nonempty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(object(owner)), memory((owner->data)[0..owner->cap]));
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
    consumes object(owner);
    consumes data[0..capacity];
    mutable owner->len, owner->cap, owner->data;
    produces empty_vector(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->cap == capacity;
    ensures owner->data == data;
} by {
    execute();
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
    execute();
    frame();
    have result == (owner->data)[index] by {
        normalize();
    }
    assumption();
    have result == old((owner->data)[index]) by {
        assumption();
    }
    assumption();
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
    step();
    step();
    step();
    step using {
        fact 0 <= index;
        fact index < owner->len;
        fact loadable(old(owner->len));
        fact loadable(old(owner->cap));
        fact loadable(old(owner->data));
        fact 1 <= owner->len;
        fact owner->len <= owner->cap;
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->cap]));
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
            have i < owner->cap by simp;
            step();
            step();
            close_invariants();
        }
    }

    ensures result == owner->len;
    ensures forall (int32 k) {
        0 <= k and k < owner->len implies (owner->data)[k] == value
    };
} by {
    step using {
        fact separate(memory(owner->len), memory(owner->cap));
        fact separate(memory(owner->len), memory(owner->data));
        fact separate(memory(owner->len), memory((owner->data)[0..owner->cap]));
        fact separate(memory(owner->cap), memory(owner->data));
        fact separate(memory(owner->cap), memory((owner->data)[0..owner->cap]));
        fact separate(memory(owner->data), memory((owner->data)[0..owner->cap]));
        fact contains(nonempty_vector(owner), memory(owner->len));
        fact contains(nonempty_vector(owner), memory(owner->cap));
        fact contains(nonempty_vector(owner), memory(owner->data));
        fact contains(nonempty_vector(owner), memory((owner->data)[0..owner->cap]));
        fact loadable(owner->len);
        fact loadable(owner->cap);
        fact loadable(owner->data);
        fact loadable((owner->data)[0..owner->cap]);
        fact 1 <= owner->len;
        fact owner->len <= owner->cap;
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->cap]));
    }
    step using {
        fact separate(memory(owner->len), memory(owner->cap));
        fact separate(memory(owner->len), memory(owner->data));
        fact separate(memory(owner->len), memory((owner->data)[0..owner->cap]));
        fact separate(memory(owner->cap), memory(owner->data));
        fact separate(memory(owner->cap), memory((owner->data)[0..owner->cap]));
        fact separate(memory(owner->data), memory((owner->data)[0..owner->cap]));
        fact contains(nonempty_vector(owner), memory(owner->len));
        fact contains(nonempty_vector(owner), memory(owner->cap));
        fact contains(nonempty_vector(owner), memory(owner->data));
        fact contains(nonempty_vector(owner), memory((owner->data)[0..owner->cap]));
        fact loadable(old(owner->len));
        fact loadable(old(owner->cap));
        fact loadable(old(owner->data));
        fact loadable(old((owner->data)[0..owner->cap]));
        fact 1 <= owner->len;
        fact owner->len <= owner->cap;
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->cap]));
    }
    have loadable(owner->len) by {
        derive(loadable(owner->len)) using {
            fact loadable(old(owner->len));
        }
    }
    have loadable(owner->cap) by {
        derive(loadable(owner->cap)) using {
            fact loadable(old(owner->cap));
        }
    }
    have loadable(owner->data) by {
        derive(loadable(owner->data)) using {
            fact loadable(old(owner->data));
        }
    }
    have loadable((owner->data)[0..owner->cap]) by {
        derive(loadable((owner->data)[0..owner->cap])) using {
            fact loadable(old((owner->data)[0..owner->cap]));
        }
    }
    have i >= 0 by {
        normalize();
    }
    have i <= owner->len by {
        derive(i <= owner->len) using {
            fact 1 <= owner->len;
        }
    }
    have forall (int32 k) { 0 <= k and k < i implies (owner->data)[k] == value } by {
        normalize();
    }
    summarize(loop(0)) using {
        fact separate(memory(owner->len), memory(owner->cap));
        fact 1 <= owner->len;
        fact owner->len <= owner->cap;
        fact loadable(old(owner->cap));
        fact loadable(old(owner->data));
        fact loadable(old(owner->len));
        fact loadable(old((owner->data)[0..owner->cap]));
        fact separate(memory(owner->len), memory(owner->data));
        fact separate(memory(owner->len), memory((owner->data)[0..owner->cap]));
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->cap]));
        fact separate(memory(owner->cap), memory(owner->data));
        fact separate(memory(owner->cap), memory((owner->data)[0..owner->cap]));
        fact separate(memory(owner->data), memory((owner->data)[0..owner->cap]));
        fact contains(nonempty_vector(owner), memory(owner->len));
        fact contains(nonempty_vector(owner), memory(owner->cap));
        fact contains(nonempty_vector(owner), memory(owner->data));
        fact contains(nonempty_vector(owner), memory((owner->data)[0..owner->cap]));
        fact loadable(owner->len);
        fact loadable(owner->cap);
        fact loadable(owner->data);
        fact loadable((owner->data)[0..owner->cap]);
        fact i >= 0;
        fact i <= owner->len;
        fact forall (int32 k) { 0 <= k and k < i implies (owner->data)[k] == value };
    }
    step using {
        fact separate(memory(owner->len), memory(owner->cap));
        fact separate(memory(owner->len), memory(owner->data));
        fact separate(memory(owner->len), memory((owner->data)[0..owner->cap]));
        fact separate(memory(owner->cap), memory(owner->data));
        fact separate(memory(owner->cap), memory((owner->data)[0..owner->cap]));
        fact separate(memory(owner->data), memory((owner->data)[0..owner->cap]));
        fact contains(nonempty_vector(owner), memory(owner->len));
        fact contains(nonempty_vector(owner), memory(owner->cap));
        fact contains(nonempty_vector(owner), memory(owner->data));
        fact contains(nonempty_vector(owner), memory((owner->data)[0..owner->cap]));
        fact loadable(old(owner->len));
        fact loadable(old(owner->cap));
        fact loadable(old(owner->data));
        fact loadable(old((owner->data)[0..owner->cap]));
        fact 1 <= owner->len;
        fact owner->len <= owner->cap;
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->cap]));
        fact i >= 0;
        fact at(statement(0).entry, i) <= at(statement(0).entry, owner->len);
        fact not i < owner->len;
    }
    frame();
    fold(nonempty_vector(owner));
    assumption();
    have result == owner->len by {
        normalize();
    }
    assumption();
    have forall (int32 k) { 0 <= k and k < owner->len implies (owner->data)[k] == value } by {
        derive(forall (int32 k) { 0 <= k and k < owner->len implies (owner->data)[k] == value }) using {
            fact not at(statement(5).entry, i) < at(statement(5).entry, owner->len);
            fact at(statement(2).entry, i) <= at(statement(2).entry, owner->len);
            fact 1 <= at(statement(5).entry, owner->len);
            fact at(statement(5).entry, i) <= at(statement(5).entry, owner->len);
            fact at(statement(5).entry, owner->len) <= at(statement(5).entry, owner->cap);
            fact at(loop(0).exit, i) >= 0;
            fact loadable(old(owner->cap));
            fact loadable(old(owner->data));
            fact loadable(old(owner->len));
            fact loadable(old((owner->data)[0..owner->cap]));
            fact separate(memory(owner->len), memory(owner->cap));
            fact separate(memory(owner->len), memory(owner->data));
            fact separate(memory(owner->len), memory((owner->data)[0..owner->cap]));
            fact separate(memory(object(owner)), memory((owner->data)[0..owner->cap]));
            fact separate(memory(owner->cap), memory(owner->data));
            fact separate(memory(owner->cap), memory((owner->data)[0..owner->cap]));
            fact separate(memory(owner->data), memory((owner->data)[0..owner->cap]));
            fact contains(nonempty_vector(owner), memory(owner->len));
            fact contains(nonempty_vector(owner), memory(owner->cap));
            fact contains(nonempty_vector(owner), memory(owner->data));
            fact contains(nonempty_vector(owner), memory((owner->data)[0..owner->cap]));
            fact forall (int32 k) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, (owner->data)[k]) == at(loop(0).exit, value) };
        }
    }
    assumption();
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
    step();
    step();
    step using {
        fact index < owner->len;
        fact 0 <= index;
        fact 1 <= owner->len;
        fact owner->len <= owner->cap;
        fact loadable(old(owner->cap));
        fact loadable(old(owner->data));
        fact loadable(old(owner->len));
    }
    reach(choose_replacement.exit)
    ensuring {
        fact replace != 0 implies selected == replacement;
        fact not (replace != 0) implies selected == original;
        fact index < index + 1;
        owns nonempty_vector(owner);
    }
    by {
        if replace != 0 {
            step();
            step using {
                fact index < owner->len;
                fact 0 <= index;
                fact 1 <= owner->len;
                fact owner->len <= owner->cap;
                fact replace != 0;
                fact original == owner->cap;
                fact loadable(old(owner->cap));
                fact loadable(old(owner->data));
                fact loadable(old(owner->len));
            }
            have replace != 0 implies selected == replacement by simp;
            have not (replace != 0) implies selected == original by simp;
            have index < index + 1 by simp;
        } else {
            step();
            step using {
                fact index < owner->len;
                fact 0 <= index;
                fact 1 <= owner->len;
                fact owner->len <= owner->cap;
                fact replace == 0;
                fact original == owner->cap;
                fact loadable(old(owner->cap));
                fact loadable(old(owner->data));
                fact loadable(old(owner->len));
            }
            have replace != 0 implies selected == replacement by simp;
            have not (replace != 0) implies selected == original by simp;
            have index < index + 1 by simp;
        }
    }
    execute();
    have index < index + 1 by { simp(); }
    frame();
    simp();
}

int32 vector_push_first(struct vector* owner, int32 value) {
    consumes empty_vector(owner);
    mutable owner->len, (owner->data)[0..1];
    produces nonempty_vector(owner);
    ensures result == 1;
    ensures owner->len == 1;
    ensures (owner->data)[0] == value;
} by {
    unfold(empty_vector(owner));
    have owner->len < owner->cap by simp;
    have 0 <= owner->len by simp;
    have owner->len < 1 by simp;
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have owner->len == 1 by simp;
    have 1 <= owner->len by simp;
    have owner->len <= owner->cap by simp;
    have separate(memory(object(owner)), memory((owner->data)[0..owner->cap])) by {
        simp();
    }
    fold(nonempty_vector(owner));
    step();
    frame();
    have result == 1 by {
        assumption();
    }
    have owner->len == 1 by {
        assumption();
    }
    have at(function.entry, loadable((owner->data + 0)[0..1])) by {
        derive(at(function.entry, loadable((owner->data + 0)[0..1]))) using {
            fact owner->len <= owner->cap;
            fact owner->len == 1;
            fact at(statement(0).entry, loadable((owner->data)[0..owner->cap]));
        }
    }
    transport(at(function.entry, loadable((owner->data + 0)[0..1])), loadable((owner->data + 0)[0..1])) using {
        fact at(function.entry, loadable((owner->data + 0)[0..1]));
    }
    have (owner->data)[0] == value by {
        derive((owner->data)[0] == value) using {
            fact at(statement(8).exit, index) == 0;
        }
    }
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 vector_clear(struct vector* owner) {
    consumes nonempty_vector(owner);
    mutable owner->len;
    produces empty_vector(owner);
    ensures result == 0;
    ensures owner->len == 0;
} by {
    unfold(nonempty_vector(owner));
    execute();
    have owner->len == 0 by simp;
    have 1 <= owner->cap by simp;
    have separate(memory(object(owner)), memory((owner->data)[0..owner->cap])) by {
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
    consumes object(owner);
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
    step using {
        fact at(statement(4).entry, 1) <= at(statement(4).entry, capacity);
        fact at(statement(2).entry, loadable(old(object(owner))));
        fact at(statement(2).entry, loadable(old(data[0..capacity])));
        fact at(statement(2).entry, separate(memory(owner[ignored..4]), memory(data[ignored..capacity])));
        fact at(statement(3).entry, observed) == at(statement(3).entry, ignored);
        fact at(statement(3).entry, owner->len) == at(statement(3).entry, 0);
        fact at(statement(4).entry, observed) == at(statement(4).entry, 1);
        fact at(statement(3).entry, owner->data) == at(statement(3).entry, data);
        fact at(statement(3).entry, owner->cap) == at(statement(3).entry, capacity);
        fact owner->cap == capacity;
        fact owner->data == data;
        fact observed == (owner->data)[0];
        fact owner->len == 1;
        fact (owner->data)[0] == first;
        fact 0 < owner->len;
        fact at(statement(4).entry, owner->len) == at(statement(4).entry, 1);
        fact at(statement(4).entry, (owner->data)[0]) == at(statement(4).entry, first);
        fact at(statement(4).entry, owner->cap) == at(statement(4).entry, capacity);
        fact at(statement(4).entry, 0) < at(statement(4).entry, owner->len);
    }
    have owner->len == owner->len by {
        normalize();
    }
    have owner->cap == owner->cap by {
        normalize();
    }
    have owner->data == owner->data by {
        normalize();
    }
    have at(statement(5).entry, owner->len) == 1 by {
        assumption();
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
    have 0 < owner->len by {
        derive(0 < owner->len) using {
            fact owner->len == 1;
        }
    }
    step using {
        fact 0 < owner->len;
        fact owner->len == 1;
    }
    step using {
        fact owner->data == (owner + 1);
        fact observed == owner->cap;
        fact ignored < owner->len;
        fact owner->len == 1;
        fact owner->len == at(statement(5).entry, owner->len);
        fact at(statement(5).entry, owner->len) == 1;
        fact at(statement(5).entry, 1) <= at(statement(5).entry, capacity);
        fact at(statement(2).entry, loadable(old(object(owner))));
        fact at(statement(2).entry, loadable(old(data[0..capacity])));
        fact at(statement(2).entry, separate(memory(owner[ignored..4]), memory(data[ignored..capacity])));
        fact at(statement(3).entry, observed) == at(statement(3).entry, ignored);
        fact at(statement(3).entry, owner->len) == at(statement(3).entry, 0);
        fact at(statement(4).entry, observed) == at(statement(4).entry, 1);
        fact at(statement(3).entry, owner->data) == data;
        fact at(statement(3).entry, owner->cap) == at(statement(3).entry, capacity);
        fact at(statement(5).entry, observed) == at(statement(5).entry, owner->data[0]);
        fact at(statement(4).entry, owner->data[0]) == at(statement(4).entry, first);
        fact owner->cap == at(statement(5).entry, owner->cap);
        fact owner->data == at(statement(5).entry, owner->data);
        fact owner->data[0] == replacement;
        fact owner->data == data;
        fact at(statement(6).entry, owner->len) == at(statement(6).entry, 1);
        fact at(statement(6).entry, 0) < at(statement(6).entry, owner->len);
        fact at(statement(5).entry, owner->data[0]) == at(statement(5).entry, first);
        fact at(statement(5).entry, owner->data) == at(statement(5).entry, data);
        fact at(statement(5).entry, 0) < at(statement(5).entry, owner->len);
        fact at(statement(4).entry, owner->len) == at(statement(4).entry, 1);
        fact at(statement(5).entry, owner->cap) == at(statement(5).entry, capacity);
        fact at(statement(4).entry, owner->data) == at(statement(4).entry, data);
        fact at(statement(4).entry, 0) < at(statement(4).entry, owner->len);
        fact owner->len == owner->len;
        fact owner->cap == owner->cap;
        fact owner->data == owner->data;
        fact separate(memory(owner->len), memory(owner->cap));
        fact separate(memory(owner->len), memory(owner->data));
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->cap]));
        fact separate(memory(owner->cap), memory(owner->data));
        fact 1 <= owner->len;
        fact owner->len <= owner->cap;
    }
    have observed == at(statement(6).entry, (owner->data)[0]) by {
        derive(observed == at(statement(6).entry, (owner->data)[0])) using {
            fact observed == owner->cap;
            fact owner->data == (owner + 1);
        }
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
    execute();
    simp();
}
