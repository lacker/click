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
    owns owner->data[0..owner->cap];
    fact owner->len == 0;
    fact 1 <= owner->cap;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

resource nonempty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
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

    ensures result == owner->data[index];
    ensures result == old(owner->data[index]);
} by {
    execute();
    frame();
    have result == owner->data[index] by {
        normalize();
    }
    assumption();
    have result == old(owner->data[index]) by {
        assumption();
    }
    assumption();
}

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;
    mutable owner->data[index..index + 1];
    owns nonempty_vector(owner);
    ensures result == value;
    ensures owner->data[index] == value;
    ensures owner->len == old(owner->len);
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    step();
    step() using {
        0 <= index;
        index < owner->len;
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        1 <= owner->len;
        owner->len <= owner->cap;
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
    }
    fold(nonempty_vector(owner));
    have index < index + 1 by simp;
    frame();
    simp();
}

int32 vector_fill(struct vector* owner, int32 value) {
    owns nonempty_vector(owner);
    mutable owner->data[0..owner->len];

    for loop(0) as fill_cells {
        invariant i >= 0 and i <= owner->len;
        mutable owner->data[0..owner->len] by frame;
        initialize by simp;
        preserve by {
            have i < owner->cap by simp;
            step();
            step();
            have i >= 0 by {
                derive using {
                    at(statement(3).entry, i) >= 0;
                    at(statement(3).entry, i) < at(statement(3).entry, owner->len);
                }
            }
            have i <= owner->len by {
                derive using {
                    at(statement(3).entry, i) < at(statement(3).entry, owner->len);
                }
            }
            close_invariants();
        }
    }

    ensures result == owner->len;
} by {
    step() using {
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(nonempty_vector(owner), memory(owner->len));
        contains(nonempty_vector(owner), memory(owner->cap));
        contains(nonempty_vector(owner), memory(owner->data));
        contains(nonempty_vector(owner), memory(owner->data[0..owner->cap]));
        loadable(owner->len);
        loadable(owner->cap);
        loadable(owner->data);
        loadable(owner->data[0..owner->cap]);
        1 <= owner->len;
        owner->len <= owner->cap;
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
    }
    step() using {
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(nonempty_vector(owner), memory(owner->len));
        contains(nonempty_vector(owner), memory(owner->cap));
        contains(nonempty_vector(owner), memory(owner->data));
        contains(nonempty_vector(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        1 <= owner->len;
        owner->len <= owner->cap;
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
    }
    have loadable(owner->len) by {
        derive using {
            loadable(old(owner->len));
        }
    }
    have loadable(owner->cap) by {
        derive using {
            loadable(old(owner->cap));
        }
    }
    have loadable(owner->data) by {
        derive using {
            loadable(old(owner->data));
        }
    }
    have loadable(owner->data[0..owner->cap]) by {
        derive using {
            loadable(old(owner->data[0..owner->cap]));
        }
    }
    have i >= 0 by {
        normalize();
    }
    have i <= owner->len by {
        derive using {
            1 <= owner->len;
        }
    }
    summarize(loop(0)) using {
        separate(memory(owner->len), memory(owner->cap));
        1 <= owner->len;
        owner->len <= owner->cap;
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->len));
        loadable(old(owner->data[0..owner->cap]));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(nonempty_vector(owner), memory(owner->len));
        contains(nonempty_vector(owner), memory(owner->cap));
        contains(nonempty_vector(owner), memory(owner->data));
        contains(nonempty_vector(owner), memory(owner->data[0..owner->cap]));
        loadable(owner->len);
        loadable(owner->cap);
        loadable(owner->data);
        loadable(owner->data[0..owner->cap]);
        i >= 0;
        i <= owner->len;
    }
    step() using {
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(nonempty_vector(owner), memory(owner->len));
        contains(nonempty_vector(owner), memory(owner->cap));
        contains(nonempty_vector(owner), memory(owner->data));
        contains(nonempty_vector(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        1 <= owner->len;
        owner->len <= owner->cap;
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        i >= 0;
        at(statement(0).entry, i) <= at(statement(0).entry, owner->len);
        not i < owner->len;
    }
    frame();
    fold(nonempty_vector(owner));
    assumption();
    have result == owner->len by {
        normalize();
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
    mutable owner->data[index..index + 1];

    for statement(3) as choose_replacement {
        assert replace == replace by auto;
    }

    ensures replace != 0 implies result == replacement;
} by {
    step();
    step();
    step() using {
        index < owner->len;
        0 <= index;
        1 <= owner->len;
        owner->len <= owner->cap;
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->len));
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
            step() using {
                index < owner->len;
                0 <= index;
                1 <= owner->len;
                owner->len <= owner->cap;
                replace != 0;
                loadable(old(owner->cap));
                loadable(old(owner->data));
                loadable(old(owner->len));
            }
            have replace != 0 implies selected == replacement by simp;
            have not (replace != 0) implies selected == original by simp;
            have index < index + 1 by simp;
        } else {
            step();
            step() using {
                index < owner->len;
                0 <= index;
                1 <= owner->len;
                owner->len <= owner->cap;
                replace == 0;
                loadable(old(owner->cap));
                loadable(old(owner->data));
                loadable(old(owner->len));
            }
            have replace != 0 implies selected == replacement by simp;
            have not (replace != 0) implies selected == original by simp;
            have index < index + 1 by simp;
        }
    }
    execute();
    have index < index + 1 by simp;
    frame();
    simp();
}

int32 vector_push_first(struct vector* owner, int32 value) {
    consumes empty_vector(owner);
    mutable owner->len, owner->data[0..1];
    produces nonempty_vector(owner);
    ensures result == 1;
    ensures owner->len == 1;
    ensures owner->data[0] == value;
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
    have separate(memory(object(owner)), memory(owner->data[0..owner->cap])) by simp;
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
        derive using {
            owner->len <= owner->cap;
            owner->len == 1;
            at(statement(0).entry, loadable(owner->data[0..owner->cap]));
        }
    }
    transport(at(function.entry, loadable((owner->data + 0)[0..1])), loadable((owner->data + 0)[0..1])) using {
        at(function.entry, loadable((owner->data + 0)[0..1]));
    }
    have owner->data[0] == value by {
        derive using {
            at(statement(8).exit, index) == 0;
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
    have separate(memory(object(owner)), memory(owner->data[0..owner->cap])) by simp;
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
    have owner->len == 0 by simp;
    have owner->cap == capacity by simp;
    execute_until(statement(4));
    have owner->len == 1 by simp;
    have 0 < owner->len by simp;
    execute_until(statement(5));
    have owner->len == 1 by simp;
    have 0 < owner->len by simp;
    step() using {
        at(statement(4).entry, 1) <= at(statement(4).entry, capacity);
        at(statement(2).entry, loadable(old(object(owner))));
        at(statement(2).entry, loadable(old(data[0..capacity])));
        at(statement(3).entry, owner->len) == at(statement(3).entry, 0);
        at(statement(4).entry, observed) == at(statement(4).entry, 1);
        at(statement(3).entry, owner->data) == at(statement(3).entry, data);
        at(statement(3).entry, owner->cap) == at(statement(3).entry, capacity);
        owner->cap == capacity;
        owner->data == data;
        observed == owner->data[0];
        owner->len == 1;
        owner->data[0] == first;
        0 < owner->len;
        at(statement(4).entry, owner->len) == at(statement(4).entry, 1);
        at(statement(4).entry, owner->data[0]) == at(statement(4).entry, first);
        at(statement(4).entry, owner->cap) == at(statement(4).entry, capacity);
        at(statement(4).entry, 0) < at(statement(4).entry, owner->len);
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
    have owner->len == at(statement(5).entry, owner->len) by simp;
    apply(int32_equality_transitive(
        owner->len,
        at(statement(5).entry, owner->len),
        1
    ));
    have owner->len == 1 by simp;
    observe(nonempty_vector(owner));
    have owner->data[0] == replacement by simp;
    have 0 < owner->len by {
        derive using {
            owner->len == 1;
        }
    }
    step() using {
        0 < owner->len;
        owner->len == 1;
    }
    have observed == owner->data[0] by simp;
    have observed == replacement by simp;
    step() using {
        owner->len == 1;
        observed == replacement;
    }
    execute();
    simp();
}
