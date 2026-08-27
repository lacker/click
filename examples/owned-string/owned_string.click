theorem incremented_zero_is_one(before: int32, after: int32) {
    requires before == 0;
    requires after == before + 1;

    ensures after == 1 by {
        rewrite(after == before + 1);
        rewrite(before == 0);
        simp();
    }
}

theorem decremented_one_is_zero(before: int32, after: int32) {
    requires before == 1;
    requires after == before - 1;

    ensures after == 0 by {
        rewrite(after == before - 1);
        rewrite(before == 1);
        simp();
    }
}

theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        simp();
    }
}

theorem pointer_equality_transitive(
    first: int32*,
    second: int32*,
    third: int32*
) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        simp();
    }
}

theorem pointer_add_zero_equals(
    base: int32*,
    offset: int32,
    target: int32*
) {
    requires base == target;
    requires offset == 0;

    ensures base + offset == target by {
        simp();
    }
}

predicate terminated_at(data: int32[], length: int32) {
    data[length] == 0
}

resource owned_string(owner: struct owned_string*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(object(owner)),
        memory(owner->data[0..owner->cap])
    );
}

resource empty_owned_string(owner: struct owned_string*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact owner->len == 0;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(object(owner)),
        memory(owner->data[0..owner->cap])
    );
}

verifying "owned_string_init.c";
verifying "owned_string_len.c";
verifying "owned_string_get.c";
verifying "owned_string_set.c";
verifying "owned_string_push.c";
verifying "owned_string_push_preserves_first.c";
verifying "owned_string_pop.c";
verifying "owned_string_pop_preserves_first.c";
verifying "owned_string_clear.c";
verifying "owned_string_pipeline.c";

int32 owned_string_init(
    struct owned_string* owner,
    int32 data[],
    int32 capacity
) {
    requires 1 <= capacity;
    consumes object(owner);
    consumes data[0..capacity];
    mutable object(owner), data[0..1];
    produces owned_string(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->cap == capacity;
    ensures owner->data == data;
    ensures data[0] == 0;
} by {
    step();
    step();
    step();
    step();
    step();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        simp();
    }
    have 0 <= owner->len by simp;
    have owner->len < owner->cap by simp;
    have separate(
        memory(object(owner)),
        memory(owner->data[0..owner->cap])
    ) by {
        simp() using {
            separate(memory(object(owner)), memory(data[0..capacity]));
            owner->data == data;
            owner->cap == capacity;
        }
    }
    fold(owned_string(owner));
    frame();
    have result == 0 by {
        normalize();
    }
    have owner->len == 0 by {
        normalize();
    }
    have owner->cap == capacity by {
        normalize();
    }
    have owner->data == data by {
        normalize();
    }
    have data[0] == 0 by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 owned_string_len(struct owned_string* owner) {
    views owned_string(owner);
    immutable by {
        step();
        frame() using {
        }
    }

    ensures result == owner->len by {
        step();
        have result == owner->len by {
            normalize();
        }
        assumption();
    }
}

int32 owned_string_get(struct owned_string* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views owned_string(owner);
    immutable by {
        step();
        frame() using {
        }
    }

    ensures result == owner->data[index] by {
        step();
        have result == owner->data[index] by {
            normalize();
        }
        assumption();
    }
}

int32 owned_string_set(
    struct owned_string* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->len;
    owns owned_string(owner);
    mutable owner->data[index..index + 1];

    ensures result == value;
    ensures owner->data[index] == value;
} by {
    unfold(owned_string(owner));
    unfold(terminated_at);
    have index < owner->cap by {
        apply(int32_lt_transitive(index, owner->len, owner->cap)) using {
            index < owner->len;
            owner->len < owner->cap;
        }
        assumption();
    }
    step();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        assumption();
    }
    have 0 <= owner->len by simp;
    have owner->len < owner->cap by simp;
    have separate(
        memory(object(owner)),
        memory(owner->data[0..owner->cap])
    ) by {
        simp();
    }
    fold(owned_string(owner));
    step();
    have index <= index by { normalize(); }
    have index < (index + 1) by {
        unfold(terminated_at);
        apply(int32_increment_strictly_increases(at(statement(1).entry, index), at(statement(1).entry, owner->len))) using {
            at(statement(1).entry, index) < at(statement(1).entry, owner->len);
        }
        assumption();
    }
    frame() using {
        0 <= index;
        loadable(owner->len);
        loadable(owner->cap);
        loadable(owner->data);
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        index < owner->len;
        index < owner->cap;
        0 <= owner->len;
        owner->len < owner->cap;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data));
        loadable(owner->data[0..owner->cap]);
        at(statement(0).entry, owner->data[owner->len]) == at(statement(0).entry, 0);
        terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        index <= index;
        index < (index + 1);
    }
    have result == value by {
        normalize();
    }
    have owner->data[index] == value by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
}

int32 owned_string_push(struct owned_string* owner, int32 value) {
    requires owner->len + 1 < owner->cap;
    owns owned_string(owner);
    mutable owner->len, (owner->data + owner->len)[0..2];
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures owner->data[old(owner->len)] == value;
    ensures owner->data[owner->len] == 0;
} by {
    unfold(owned_string(owner));
    step();
    step();
    step();
    step();
    step();
    have at(statement(4).entry, owner->data) == old(owner->data) by {
        normalize();
    }
    have owner->data == old(owner->data) by {
        transport(
            at(statement(4).entry, owner->data) == old(owner->data),
            owner->data == old(owner->data)
        ) using {
            at(statement(4).entry, owner->data) == old(owner->data);
            at(statement(4).entry, separate(
                memory(object(owner)),
                memory(owner->data[0..owner->cap])
            ));
            at(statement(4).entry, (index + 1)) < at(statement(4).entry, owner->cap);
            at(statement(4).entry, index) < at(statement(4).entry, owner->cap);
            at(statement(3).entry, 0) <= at(statement(3).entry, owner->len);
            at(statement(3).exit, owner->len) == at(statement(3).entry, (index + 1));
        }
        assumption();
    }
    have owner->data == at(statement(4).entry, owner->data) by {
        assumption();
    }
    have owner->len == at(statement(4).entry, (index + 1)) by {
        transport(
            at(statement(3).exit, owner->len) == at(statement(3).entry, (index + 1)),
            owner->len == at(statement(4).entry, (index + 1))
        ) using {
            at(statement(3).exit, owner->len) == at(statement(3).entry, (index + 1));
            at(statement(4).entry, separate(
                memory(owner->len),
                memory(owner->data[0..owner->cap])
            ));
            at(statement(4).entry, separate(memory(owner->len), memory(owner->data)));
            at(statement(4).entry, (index + 1)) < at(statement(4).entry, owner->cap);
            at(statement(4).entry, index) < at(statement(4).entry, owner->cap);
            at(statement(3).entry, 0) <= at(statement(3).entry, owner->len);
        }
        assumption();
    }
    have 0 <= at(statement(4).entry, index) by {
        assumption();
    }
    have 0 <= owner->len by {
        apply(int32_increment_lower_bound(
            at(statement(4).entry, index),
            0,
            at(statement(4).entry, owner->cap)
        )) using {
            0 <= at(statement(4).entry, index);
            at(statement(4).entry, index) < at(statement(4).entry, owner->cap);
        }
        rewrite(owner->len == at(statement(4).entry, (index + 1)));
        assumption();
    }
    have owner->data[owner->len] == 0 by {
        rewrite(owner->data == at(statement(4).entry, owner->data));
        rewrite(owner->len == at(statement(4).entry, (index + 1)));
        assumption();
    }
    step();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        assumption();
    }
    have owner->len < owner->cap by {
        have at(statement(4).entry, owner->len) ==
            at(statement(4).entry, (index + 1)) by {
            normalize();
        }
        have at(statement(4).entry, owner->len) <
            at(statement(4).entry, owner->cap) by {
            assumption();
        }
        transport(
            at(statement(4).entry, owner->len) <
                at(statement(4).entry, owner->cap),
            owner->len < owner->cap
        ) using {
            at(statement(4).entry, owner->len) <
                at(statement(4).entry, owner->cap);
            at(statement(4).entry, separate(memory(owner->len), memory(owner->cap)));
            at(statement(4).entry, separate(
                memory(owner->len),
                memory(owner->data[0..owner->cap])
            ));
            at(statement(4).entry, separate(
                memory(owner->cap),
                memory(owner->data[0..owner->cap])
            ));
            at(statement(4).entry, (index + 1)) < at(statement(4).entry, owner->cap);
            at(statement(4).entry, index) < at(statement(4).entry, owner->cap);
            at(statement(3).entry, 0) <= at(statement(3).entry, owner->len);
        }
        assumption();
    }
    have separate(memory(object(owner)), memory(owner->data[0..owner->cap])) by {
        transport(
            at(statement(4).entry, separate(
                memory(object(owner)),
                memory(owner->data[0..owner->cap])
            )),
            separate(memory(object(owner)), memory(owner->data[0..owner->cap]))
        ) using {
            at(statement(4).entry, separate(memory(owner->len), memory(owner->cap)));
            at(statement(4).entry, separate(memory(owner->len), memory(owner->data)));
            at(statement(4).entry, separate(memory(object(owner)), memory(owner->data[0..owner->cap])));
            at(statement(4).entry, separate(memory(owner->cap), memory(owner->data)));
            at(statement(4).entry, loadable(old(owner->len)));
            at(statement(4).entry, loadable(old(owner->cap)));
            at(statement(4).entry, loadable(old(owner->data)));
            at(statement(4).entry, loadable(old(owner->data[0..owner->cap])));
            at(statement(3).entry, 0) <= at(statement(3).entry, owner->len);
            at(statement(4).entry, (index + 1)) < at(statement(4).entry, owner->cap);
            at(statement(4).entry, index) < at(statement(4).entry, owner->cap);
            at(statement(4).entry, separate(memory(owner->len), memory(owner->data[0..owner->cap])));
            at(statement(4).entry, separate(memory(owner->cap), memory(owner->data[0..owner->cap])));
            at(statement(4).entry, separate(memory(owner->data), memory(owner->data[0..owner->cap])));
            at(statement(4).entry, contains(owned_string(owner), memory(owner->len)));
            at(statement(4).entry, contains(owned_string(owner), memory(owner->cap)));
            at(statement(4).entry, contains(owned_string(owner), memory(owner->data)));
            at(statement(4).entry, contains(owned_string(owner), memory(owner->data[0..owner->cap])));
            terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
            terminated_at(owner->data, owner->len);
            0 <= owner->len;
            owner->len < owner->cap;
        }
        assumption();
    }
    have at(statement(4).entry, owner->cap) == old(owner->cap) by {
        normalize();
    }
    have owner->cap == old(owner->cap) by {
        transport(
            at(statement(4).entry, owner->cap) == old(owner->cap),
            owner->cap == old(owner->cap)
        ) using {
            at(statement(4).entry, owner->cap) == old(owner->cap);
            at(statement(4).entry, separate(memory(owner->len), memory(owner->cap)));
            at(statement(4).entry, separate(
                memory(owner->cap),
                memory(owner->data[0..owner->cap])
            ));
            at(statement(4).entry, loadable(old(owner->cap)));
        }
        assumption();
    }
    fold(owned_string(owner));
    frame() using {
    }
    have at(statement(3).entry, index) == old(owner->len) by {
        normalize();
    }
    have owner->len == (old(owner->len) + 1) by {
        have owner->len == at(statement(3).entry, (index + 1)) by {
            transport(
                at(statement(3).exit, owner->len) == at(statement(3).entry, (index + 1)),
                owner->len == at(statement(3).entry, (index + 1))
            ) using {
                at(statement(3).exit, owner->len) == at(statement(3).entry, (index + 1));
                at(statement(4).entry, separate(
                    memory(owner->len),
                    memory(owner->data[0..owner->cap])
                ));
                at(statement(4).entry, separate(memory(owner->len), memory(owner->data)));
                at(statement(4).entry, (index + 1)) < at(statement(4).entry, owner->cap);
                at(statement(4).entry, index) < at(statement(4).entry, owner->cap);
                at(statement(3).entry, 0) <= at(statement(3).entry, owner->len);
            }
            assumption();
        }
        rewrite(owner->len == at(statement(3).entry, (index + 1)));
        assumption();
    }
    have result == (old(owner->len) + 1) by {
        assumption();
    }
    have owner->data[old(owner->len)] == value by {
        rewrite(owner->data == old(owner->data));
        assumption();
    }
    have owner->data[owner->len] == 0 by {
        rewrite(owner->len == (old(owner->len) + 1));
        rewrite(owner->data == old(owner->data));
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 owned_string_push_preserves_first(
    struct owned_string* owner,
    int32 value
) {
    let data = old(owner->data);

    requires 1 <= owner->len;
    requires owner->len + 1 < owner->cap;
    owns owned_string(owner);
    mutable owner->len, (owner->data + owner->len)[0..2];

    ensures result == old(owner->len) + 1;
    ensures data[0] == old(data[0]);
} by {
    step();
    step();
    step();
    have owner->data[owner->len] == 0 by {
        assumption();
    }
    have 0 == 0 by {
        normalize();
    }
    frame() using {
    }
    have result == (old(owner->len) + 1) by {
        assumption();
    }
    have (let data = old(owner->data); old(owner->data)[0]) == (let data = old(owner->data); old(old(owner->data)[0])) by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
}

int32 owned_string_pop(struct owned_string* owner) {
    requires 1 <= owner->len;
    owns owned_string(owner);
    mutable owner->len, (owner->data + (owner->len - 1))[0..1];
    ensures result == old(owner->data[owner->len - 1]);
    ensures owner->len == old(owner->len) - 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures owner->data[owner->len] == 0;
} by {
    unfold(owned_string(owner));
    have 0 <= (owner->len - 1) by {
        have 0 < owner->len by {
            apply(int32_successor_le_implies_lt(0, owner->len)) using {
                1 <= owner->len;
            }
            assumption();
        }
        apply(int32_positive_predecessor_is_nonnegative(owner->len)) using {
            0 < owner->len;
        }
        assumption();
    }
    have (owner->len - 1) < owner->len by {
        have 0 < owner->len by {
            apply(int32_successor_le_implies_lt(0, owner->len)) using {
                1 <= owner->len;
            }
            assumption();
        }
        apply(int32_positive_predecessor_strictly_decreases(owner->len)) using {
            0 < owner->len;
        }
        assumption();
    }
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        normalize();
    }
    have 0 <= owner->len by {
        assumption();
    }
    have owner->len < owner->cap by {
        apply(int32_lt_transitive(at(statement(5).entry, (owner->len - 1)), at(statement(5).entry, owner->len), at(statement(5).entry, owner->cap))) using {
            at(statement(5).entry, (owner->len - 1)) < at(statement(5).entry, owner->len);
            at(statement(5).entry, owner->len) < at(statement(5).entry, owner->cap);
        }
        assumption();
    }
    have separate(memory(object(owner)), memory(owner->data[0..owner->cap])) by {
        assumption();
    }
    fold(owned_string(owner));
    frame() using {
    }
    have loadable(old((owner->data + (owner->len - 1))[0..1])) by {
        transport(at(statement(6).entry, loadable(old(owner->data[0..owner->cap]))), loadable(old((owner->data + (owner->len - 1))[0..1]))) using {
            at(statement(6).exit, index) < old(owner->len);
            old(owner->len) < owner->cap;
            1 <= old(owner->len);
            at(statement(6).entry, loadable(old(owner->data[0..owner->cap])));
        }
        assumption();
    }
    have result == old(owner->data[(owner->len - 1)]) by {
        normalize();
    }
    have owner->len == (old(owner->len) - 1) by {
        normalize();
    }
    have owner->cap == old(owner->cap) by {
        normalize();
    }
    have owner->data == old(owner->data) by {
        normalize();
    }
    have owner->data[owner->len] == 0 by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 owned_string_pop_preserves_first(struct owned_string* owner) {
    let data = old(owner->data);

    requires 2 <= owner->len;
    owns owned_string(owner);
    mutable owner->len, (owner->data + (owner->len - 1))[0..1];

    ensures result == old(owner->data[owner->len - 1]);
    ensures data[0] == old(data[0]);
} by {
    step();
    step();
    step();
    have 0 == 0 by {
        normalize();
    }
    frame() using {
        owner->len < owner->cap;
        2 <= owner->len;
        loadable(owner->cap);
        loadable(owner->data);
        loadable(owner->len);
        owner->cap == at(statement(0).entry, owner->cap);
        owner->data == at(statement(0).entry, owner->data);
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        loadable(owner->data[0..owner->cap]);
        0 <= owner->len;
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        terminated_at(owner->data, owner->len);
        0 == 0;
    }
    have result == old(owner->data[(owner->len - 1)]) by {
        assumption();
    }
    have (let data = old(owner->data); old(owner->data)[0]) == (let data = old(owner->data); old(old(owner->data)[0])) by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
}

int32 owned_string_clear(struct owned_string* owner) {
    owns owned_string(owner);
    mutable owner->len, owner->data[0..1];
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->data[0] == 0;
} by {
    unfold(owned_string(owner));
    step();
    step();
    step();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        normalize();
    }
    have 0 <= owner->len by simp;
    have owner->len < owner->cap by {
        apply(int32_le_lt_transitive(at(statement(0).entry, 0), at(statement(0).entry, owner->len), at(statement(0).entry, owner->cap))) using {
            at(statement(0).entry, 0) <= at(statement(0).entry, owner->len);
            at(statement(0).entry, owner->len) < at(statement(0).entry, owner->cap);
        }
        assumption();
    }
    have separate(
        memory(object(owner)),
        memory(owner->data[0..owner->cap])
    ) by {
        simp();
    }
    fold(owned_string(owner));
    frame();
    have result == 0 by {
        normalize();
    }
    have owner->len == 0 by {
        normalize();
    }
    have owner->data[0] == 0 by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 owned_string_pipeline(
    struct owned_string* owner,
    int32 data[],
    int32 capacity,
    int32 first
) {
    requires 2 <= capacity;
    consumes object(owner);
    consumes data[0..capacity];
    produces empty_owned_string(owner);
    ensures result == first;
} by {
    step();
    step();
    step();
    have ignored == 0 by {
        assumption();
    }
    have owner->len == 0 by {
        assumption();
    }
    have owner->cap == capacity by {
        assumption();
    }
    have (owner->len + 1) < owner->cap by {
        rewrite(owner->cap == capacity);
        rewrite(owner->len == 0);
        apply(int32_successor_le_implies_lt(1, at(statement(2).entry, capacity))) using {
            at(statement(2).entry, 2) <= at(statement(2).entry, capacity);
        }
        assumption();
    }
    step();
    have owner->len == 1 by {
        rewrite(owner->len == at(statement(3).entry, owner->len + 1));
        rewrite(at(statement(3).entry, owner->len) == at(statement(3).entry, 0));
        normalize();
    }
    have 0 < owner->len by {
        rewrite(owner->len == 1);
        normalize();
    }
    have owner->data[at(statement(3).entry, owner->len)] == first by {
        assumption();
    }
    have owner->data[0] == first by {
        rewrite(first == owner->data[at(statement(3).entry, owner->len)]);
        rewrite(at(statement(3).entry, owner->len) == at(statement(3).entry, 0));
        normalize();
    }
    step();
    have 1 <= owner->len by {
        rewrite(owner->len == 1);
        normalize();
    }
    have observed == first by {
        rewrite(first == owner->data[0]);
        assumption();
    }
    step();
    have owner->len == at(statement(5).entry, owner->len) - 1 by {
        assumption();
    }
    have at(statement(5).entry, owner->len) == 1 by {
        assumption();
    }
    apply(decremented_one_is_zero(at(statement(5).entry, owner->len), owner->len)) using {
        at(statement(5).entry, owner->len) == 1;
        owner->len == (at(statement(5).entry, owner->len) - 1);
    }
    have owner->len == 0 by {
        assumption();
    }
    unfold(owned_string(owner));
    fold(empty_owned_string(owner));
    have observed == first by {
        assumption();
    }
    step();
    have result == at(statement(6).entry, observed) by {
        normalize();
    }
    have at(statement(6).entry, observed) == first by {
        assumption();
    }
    have result == first by {
        assumption();
    }
    assumption();
    assumption();
}
