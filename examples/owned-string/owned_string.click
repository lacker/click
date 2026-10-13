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
        memory(*owner),
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
        memory(*owner),
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
    consumes *owner;
    consumes data[0..capacity];
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
    have 0 <= owner->len;
    have owner->len < owner->cap;
    have separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    ) by {
        simp() using {
            separate(memory(*owner), memory(data[0..capacity]));
            owner->data == data;
            owner->cap == capacity;
        }
    }
    fold(owned_string(owner));
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

    ensures result == owner->len by {
        step();
        assumption();
    }
}

int32 owned_string_get(struct owned_string* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views owned_string(owner);

    ensures result == owner->data[index] by {
        step();
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

    ensures result == value;
    ensures owner->data[index] == value;
} by {
    unfold(owned_string(owner));
    unfold(terminated_at);
    step();
    have separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    ) by {
        simp();
    }
    fold(owned_string(owner));
    step();
    assumption();
    assumption();
    assumption();
}

int32 owned_string_push(struct owned_string* owner, int32 value) {
    requires owner->len + 1 < owner->cap;
    owns owned_string(owner);
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
    have owner->len == at(statement(4).entry, (index + 1)) by auto;
    step();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        assumption();
    }
    fold(owned_string(owner));
    have owner->len == (old(owner->len) + 1) by {
        rewrite(owner->len == at(statement(3).entry, (index + 1)));
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

    ensures result == old(owner->len) + 1;
    ensures data[0] == old(data[0]);
} by {
    step();
    step();
    step();
    assumption();
    assumption();
    assumption();
}

int32 owned_string_pop(struct owned_string* owner) {
    requires 1 <= owner->len;
    owns owned_string(owner);
    ensures result == old(owner->data[owner->len - 1]);
    ensures owner->len == old(owner->len) - 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures owner->data[owner->len] == 0;
} by {
    unfold(owned_string(owner));
    have (owner->len - 1) < owner->len by {
        have 0 < owner->len by auto;
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
    fold(owned_string(owner));
    have owner->data[owner->len] == 0 by auto;
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

    ensures result == old(owner->data[owner->len - 1]);
    ensures data[0] == old(data[0]);
} by {
    step();
    step();
    step();
    assumption();
    assumption();
    assumption();
}

int32 owned_string_clear(struct owned_string* owner) {
    owns owned_string(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->data[0] == 0;
} by {
    unfold(owned_string(owner));
    step();
    step();
    step();
    have terminated_at(owner->data, owner->len) by auto;
    have 0 <= owner->len;
    have separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    ) by {
        simp();
    }
    fold(owned_string(owner));
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
    consumes *owner;
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
        apply(int32_increment_less_equal_implies_less_than(1, at(statement(2).entry, capacity))) using {
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
