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

predicate terminated_at(int32 data[], int32 length) {
    data[length] == 0
}

resource owned_string(owner: struct owned_string*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(owner[0..4]),
        memory((owner->data)[0..owner->cap])
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
    consumes owner[0..4];
    consumes data[0..capacity];
    mutable owner[0..4], data[0..1];
    produces owned_string(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->cap == capacity;
    ensures owner->data == data;
    ensures data[0] == 0;
} by {
    execute_rest();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        simp();
    }
    have 0 <= owner->len by { simp(); }
    have owner->len < owner->cap by { simp(); }
    have separate(
        memory(owner[0..4]),
        memory((owner->data)[0..owner->cap])
    ) by {
        simp();
    }
    fold(owned_string(owner));
    frame();
    simp();
}

int32 owned_string_len(struct owned_string* owner) {
    views owned_string(owner);
    immutable;

    ensures result == owner->len by auto;
}

int32 owned_string_get(struct owned_string* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views owned_string(owner);
    immutable;

    ensures result == (owner->data)[index] by auto;
}

int32 owned_string_set(
    struct owned_string* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->len;
    owns owned_string(owner);
    mutable (owner->data)[index..index + 1];

    ensures result == value;
    ensures (owner->data)[index] == value;
} by {
    unfold(owned_string(owner));
    unfold(terminated_at);
    have index < load_int32((owner + 1)) by { simp(); }
    step using {
        fact 0 <= index;
        fact index < load_int32(owner);
        fact index < load_int32((owner + 1));
        fact loadable(owner[0..1]);
        fact loadable((owner + 1)[0..1]);
        fact loadable((owner + 2)[0..2]);
        fact 0 <= load_int32(owner);
        fact load_int32(owner) < load_int32((owner + 1));
        fact terminated_at(load_int32_pointer((owner + 2)), load_int32(owner));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact load_int32_pointer((owner + 2))[load_int32(owner)] == 0;
    }
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        assumption();
    }
    have load_int32_pointer((owner + 2))[load_int32(owner)] == 0 by {
        assumption();
    }
    have 0 <= owner->len by { simp(); }
    have owner->len < owner->cap by { simp(); }
    have separate(
        memory(owner[0..4]),
        memory((owner->data)[0..owner->cap])
    ) by {
        simp();
    }
    fold(owned_string(owner));
    execute_step();
    have index < index + 1 by { simp(); }
    frame();
    have result == value by {
        normalize();
    }
    have load_int32_pointer((owner + 2))[index] == value by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
}

int32 owned_string_push(struct owned_string* owner, int32 value) {
    requires owner->len + 1 < owner->cap;
    owns owned_string(owner);
    mutable owner[0..1], (owner->data + owner->len)[0..2];
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures (owner->data)[old(owner->len)] == value;
    ensures (owner->data)[owner->len] == 0;
} by {
    unfold(owned_string(owner));
    execute_step();
    execute_step();
    execute_step();
    step using {
        fact at(statement(0).entry, (load_int32(owner) + 1)) < at(statement(0).entry, load_int32((owner + 1)));
        fact separate(memory(owner[0..1]), memory(owner[1..2]));
        fact separate(memory(owner[0..1]), memory(owner[2..4]));
        fact separate(memory(owner[0..1]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[1..2]), memory(owner[2..4]));
        fact separate(memory(owner[1..2]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[2..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact contains(owned_string(owner), memory(owner[0..1]));
        fact contains(owned_string(owner), memory(owner[1..2]));
        fact contains(owned_string(owner), memory(owner[2..4]));
        fact contains(owned_string(owner), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact loadable(old(owner[0..1]));
        fact loadable(old(owner[1..2]));
        fact loadable(old(owner[2..4]));
        fact loadable(old(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact at(statement(0).entry, 0) <= at(statement(0).entry, load_int32(owner));
        fact at(statement(0).entry, load_int32(owner)) < at(statement(0).entry, load_int32((owner + 1)));
        fact terminated_at(at(statement(0).entry, load_int32_pointer((owner + 2))), at(statement(0).entry, load_int32(owner)));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
    }
    step using {
        fact separate(memory(owner[0..1]), memory(owner[1..2]));
        fact separate(memory(owner[0..1]), memory(owner[2..4]));
        fact separate(memory(owner[0..1]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[1..2]), memory(owner[2..4]));
        fact separate(memory(owner[1..2]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[2..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact contains(owned_string(owner), memory(owner[0..1]));
        fact contains(owned_string(owner), memory(owner[1..2]));
        fact contains(owned_string(owner), memory(owner[2..4]));
        fact contains(owned_string(owner), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact loadable(old(owner[0..1]));
        fact loadable(old(owner[1..2]));
        fact loadable(old(owner[2..4]));
        fact loadable(old(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact at(statement(0).entry, 0) <= at(statement(0).entry, load_int32(owner));
        fact terminated_at(at(statement(0).entry, load_int32_pointer((owner + 2))), at(statement(0).entry, load_int32(owner)));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact at(statement(4).entry, (index + 1)) < at(statement(4).entry, *(owner + 1));
        fact at(statement(4).entry, index) < at(statement(4).entry, *(owner + 1));
        fact at(statement(0).entry, (load_int32(owner) + 1)) < at(statement(0).entry, load_int32((owner + 1)));
        fact at(statement(0).entry, load_int32(owner)) < at(statement(0).entry, load_int32((owner + 1)));
    }
    execute_step();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        simp();
    }
    have 0 <= owner->len by { simp(); }
    have owner->len < owner->cap by { simp(); }
    have separate(
        memory(owner[0..4]),
        memory((owner->data)[0..owner->cap])
    ) by {
        simp();
    }
    fold(owned_string(owner));
    frame();
    simp();
}

int32 owned_string_push_preserves_first(
    struct owned_string* owner,
    int32 value
) {
    let data = old(owner->data);

    requires 1 <= owner->len;
    requires owner->len + 1 < owner->cap;
    owns owned_string(owner);
    mutable owner[0..1], (owner->data + owner->len)[0..2];

    ensures result == old(owner->len) + 1;
    ensures data[0] == old(data[0]);
} by {
    execute_step();
    step using {
        fact (load_int32(owner) + 1) < load_int32((owner + 1));
        fact *owner < *(owner + 1);
        fact 1 <= load_int32(owner);
        fact loadable(old((owner + 1)[0..1]));
        fact loadable(old((owner + 2)[0..2]));
        fact loadable(old(owner[0..1]));
    }
    execute_step();
    frame();
    simp();
}

int32 owned_string_pop(struct owned_string* owner) {
    requires 1 <= owner->len;
    owns owned_string(owner);
    mutable owner[0..1], (owner->data + (owner->len - 1))[0..1];
    ensures result == old((owner->data)[owner->len - 1]);
    ensures owner->len == old(owner->len) - 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures (owner->data)[owner->len] == 0;
} by {
    unfold(owned_string(owner));
    have 0 <= owner->len - 1 by {
        simp();
    }
    have owner->len - 1 < owner->len by {
        simp();
    }
    step using {
        fact 1 <= load_int32(owner);
        fact separate(memory(owner[0..1]), memory(owner[1..2]));
        fact separate(memory(owner[0..1]), memory(owner[2..4]));
        fact separate(memory(owner[0..1]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[1..2]), memory(owner[2..4]));
        fact separate(memory(owner[1..2]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[2..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact contains(owned_string(owner), memory(owner[0..1]));
        fact contains(owned_string(owner), memory(owner[1..2]));
        fact contains(owned_string(owner), memory(owner[2..4]));
        fact contains(owned_string(owner), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact loadable(owner[0..1]);
        fact loadable(owner[1..2]);
        fact loadable(owner[2..4]);
        fact loadable(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]);
        fact 0 <= load_int32(owner);
        fact load_int32(owner) < load_int32((owner + 1));
        fact terminated_at(load_int32_pointer((owner + 2)), load_int32(owner));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= (load_int32(owner) - 1);
        fact (load_int32(owner) - 1) < load_int32(owner);
    }
    step using {
        fact 1 <= load_int32(owner);
        fact separate(memory(owner[0..1]), memory(owner[1..2]));
        fact separate(memory(owner[0..1]), memory(owner[2..4]));
        fact separate(memory(owner[0..1]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[1..2]), memory(owner[2..4]));
        fact separate(memory(owner[1..2]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[2..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact contains(owned_string(owner), memory(owner[0..1]));
        fact contains(owned_string(owner), memory(owner[1..2]));
        fact contains(owned_string(owner), memory(owner[2..4]));
        fact contains(owned_string(owner), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact loadable(old(owner[0..1]));
        fact loadable(old(owner[1..2]));
        fact loadable(old(owner[2..4]));
        fact loadable(old(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= load_int32(owner);
        fact load_int32(owner) < load_int32((owner + 1));
        fact terminated_at(at(statement(0).entry, load_int32_pointer((owner + 2))), at(statement(0).entry, load_int32(owner)));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= (load_int32(owner) - 1);
        fact (load_int32(owner) - 1) < load_int32(owner);
    }
    step using {
        fact 1 <= load_int32(owner);
        fact separate(memory(owner[0..1]), memory(owner[1..2]));
        fact separate(memory(owner[0..1]), memory(owner[2..4]));
        fact separate(memory(owner[0..1]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[1..2]), memory(owner[2..4]));
        fact separate(memory(owner[1..2]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[2..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact contains(owned_string(owner), memory(owner[0..1]));
        fact contains(owned_string(owner), memory(owner[1..2]));
        fact contains(owned_string(owner), memory(owner[2..4]));
        fact contains(owned_string(owner), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact loadable(old(owner[0..1]));
        fact loadable(old(owner[1..2]));
        fact loadable(old(owner[2..4]));
        fact loadable(old(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= load_int32(owner);
        fact load_int32(owner) < load_int32((owner + 1));
        fact terminated_at(at(statement(0).entry, load_int32_pointer((owner + 2))), at(statement(0).entry, load_int32(owner)));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= (load_int32(owner) - 1);
        fact (load_int32(owner) - 1) < load_int32(owner);
    }
    step using {
        fact 1 <= load_int32(owner);
        fact separate(memory(owner[0..1]), memory(owner[1..2]));
        fact separate(memory(owner[0..1]), memory(owner[2..4]));
        fact separate(memory(owner[0..1]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[1..2]), memory(owner[2..4]));
        fact separate(memory(owner[1..2]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[2..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact contains(owned_string(owner), memory(owner[0..1]));
        fact contains(owned_string(owner), memory(owner[1..2]));
        fact contains(owned_string(owner), memory(owner[2..4]));
        fact contains(owned_string(owner), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact loadable(old(owner[0..1]));
        fact loadable(old(owner[1..2]));
        fact loadable(old(owner[2..4]));
        fact loadable(old(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= load_int32(owner);
        fact load_int32(owner) < load_int32((owner + 1));
        fact terminated_at(at(statement(0).entry, load_int32_pointer((owner + 2))), at(statement(0).entry, load_int32(owner)));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= (load_int32(owner) - 1);
        fact (load_int32(owner) - 1) < load_int32(owner);
    }
    step using {
        fact 1 <= load_int32(owner);
        fact separate(memory(owner[0..1]), memory(owner[1..2]));
        fact separate(memory(owner[0..1]), memory(owner[2..4]));
        fact separate(memory(owner[0..1]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[1..2]), memory(owner[2..4]));
        fact separate(memory(owner[1..2]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[2..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact contains(owned_string(owner), memory(owner[0..1]));
        fact contains(owned_string(owner), memory(owner[1..2]));
        fact contains(owned_string(owner), memory(owner[2..4]));
        fact contains(owned_string(owner), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact loadable(old(owner[0..1]));
        fact loadable(old(owner[1..2]));
        fact loadable(old(owner[2..4]));
        fact loadable(old(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= load_int32(owner);
        fact load_int32(owner) < load_int32((owner + 1));
        fact terminated_at(at(statement(0).entry, load_int32_pointer((owner + 2))), at(statement(0).entry, load_int32(owner)));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= (load_int32(owner) - 1);
        fact (load_int32(owner) - 1) < load_int32(owner);
    }
    step using {
        fact 1 <= load_int32(owner);
        fact separate(memory(owner[0..1]), memory(owner[1..2]));
        fact separate(memory(owner[0..1]), memory(owner[2..4]));
        fact separate(memory(owner[0..1]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[1..2]), memory(owner[2..4]));
        fact separate(memory(owner[1..2]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[2..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact contains(owned_string(owner), memory(owner[0..1]));
        fact contains(owned_string(owner), memory(owner[1..2]));
        fact contains(owned_string(owner), memory(owner[2..4]));
        fact contains(owned_string(owner), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact loadable(old(owner[0..1]));
        fact loadable(old(owner[1..2]));
        fact loadable(old(owner[2..4]));
        fact loadable(old(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= load_int32(owner);
        fact load_int32(owner) < load_int32((owner + 1));
        fact terminated_at(at(statement(0).entry, load_int32_pointer((owner + 2))), at(statement(0).entry, load_int32(owner)));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact 0 <= (load_int32(owner) - 1);
        fact (load_int32(owner) - 1) < load_int32(owner);
    }
    step using {
        fact at(statement(0).entry, 1) <= at(statement(0).entry, load_int32(owner));
        fact separate(memory(owner[0..1]), memory(owner[1..2]));
        fact separate(memory(owner[0..1]), memory(owner[2..4]));
        fact separate(memory(owner[0..1]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[1..2]), memory(owner[2..4]));
        fact separate(memory(owner[1..2]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact separate(memory(owner[2..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact contains(owned_string(owner), memory(owner[0..1]));
        fact contains(owned_string(owner), memory(owner[1..2]));
        fact contains(owned_string(owner), memory(owner[2..4]));
        fact contains(owned_string(owner), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact loadable(old(owner[0..1]));
        fact loadable(old(owner[1..2]));
        fact loadable(old(owner[2..4]));
        fact loadable(old(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact at(statement(0).entry, 0) <= at(statement(0).entry, load_int32(owner));
        fact at(statement(0).entry, load_int32(owner)) < at(statement(0).entry, load_int32((owner + 1)));
        fact terminated_at(at(statement(0).entry, load_int32_pointer((owner + 2))), at(statement(0).entry, load_int32(owner)));
        fact separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));
        fact at(statement(0).entry, 0) <= at(statement(0).entry, (load_int32(owner) - 1));
        fact at(statement(0).entry, (load_int32(owner) - 1)) < at(statement(0).entry, load_int32(owner));
    }
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        simp();
    }
    have 0 <= owner->len by { simp(); }
    have owner->len < owner->cap by { simp(); }
    have separate(
        memory(owner[0..4]),
        memory((owner->data)[0..owner->cap])
    ) by {
        simp();
    }
    fold(owned_string(owner));
    frame();
    have loadable(old((load_int32_pointer((owner + 2)) + (load_int32(owner) - 1))[0..1])) by {
        calculate(loadable(old((load_int32_pointer((owner + 2)) + (load_int32(owner) - 1))[0..1]))) using {
            fact at(statement(6).exit, index) < old(*owner);
            fact old(*owner) < *(owner + 1);
            fact 0 <= at(statement(6).exit, index);
            fact 0 <= old(*owner);
            fact 1 <= old(*owner);
            fact terminated_at(at(statement(0).entry, load_int32_pointer((owner + 2))), at(statement(0).entry, load_int32(owner)));
            fact at(statement(6).entry, loadable(old(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))])));
            fact at(statement(6).entry, separate(memory(owner[0..1]), memory(owner[1..2])));
            fact at(statement(6).entry, separate(memory(owner[0..1]), memory(owner[2..4])));
            fact at(statement(6).entry, separate(memory(owner[0..1]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))])));
            fact at(statement(6).entry, separate(memory(owner[0..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))])));
            fact at(statement(6).entry, separate(memory(owner[1..2]), memory(owner[2..4])));
            fact at(statement(6).entry, separate(memory(owner[1..2]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))])));
            fact at(statement(6).entry, separate(memory(owner[2..4]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))])));
            fact at(statement(6).entry, contains(owned_string(owner), memory(owner[0..1])));
            fact at(statement(6).entry, contains(owned_string(owner), memory(owner[1..2])));
            fact at(statement(6).entry, contains(owned_string(owner), memory(owner[2..4])));
            fact at(statement(6).entry, contains(owned_string(owner), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))])));
        }
    }
    have result == old(load_int32_pointer((owner + 2))[(load_int32(owner) - 1)]) by {
        normalize();
    }
    have load_int32(owner) == (old(load_int32(owner)) - 1) by {
        normalize();
    }
    have load_int32((owner + 1)) == old(load_int32((owner + 1))) by {
        normalize();
    }
    have load_int32_pointer((owner + 2)) == old(load_int32_pointer((owner + 2))) by {
        normalize();
    }
    have load_int32_pointer((owner + 2))[load_int32(owner)] == 0 by {
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
    mutable owner[0..1], (owner->data + (owner->len - 1))[0..1];

    ensures result == old((owner->data)[owner->len - 1]);
    ensures data[0] == old(data[0]);
} by {
    execute_step();
    step using {
        fact *owner < *(owner + 1);
        fact 2 <= load_int32(owner);
        fact loadable(old((owner + 1)[0..1]));
        fact loadable(old((owner + 2)[0..2]));
        fact loadable(old(owner[0..1]));
    }
    execute_step();
    frame();
    simp();
}

int32 owned_string_clear(struct owned_string* owner) {
    owns owned_string(owner);
    mutable owner[0..1], (owner->data)[0..1];
    ensures result == 0;
    ensures owner->len == 0;
    ensures (owner->data)[0] == 0;
} by {
    unfold(owned_string(owner));
    execute_rest();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        simp();
    }
    have 0 <= owner->len by { simp(); }
    have owner->len < owner->cap by { simp(); }
    have separate(
        memory(owner[0..4]),
        memory((owner->data)[0..owner->cap])
    ) by {
        simp();
    }
    fold(owned_string(owner));
    frame();
    simp();
}

int32 owned_string_pipeline(
    struct owned_string* owner,
    int32 data[],
    int32 capacity,
    int32 first
) {
    requires 2 <= capacity;
    consumes owner[0..4];
    consumes data[0..capacity];
    produces owned_string(owner);
    ensures owner->len == 0;
    ensures result == first;
} by {
    execute_until(statement(3));
    have owner->len == 0 by {
        simp();
    }
    have owner->cap == capacity by {
        simp();
    }
    have owner->len + 1 < owner->cap by {
        simp();
    }
    step using {
        fact (load_int32(owner) + 1) < load_int32((owner + 1));
        fact 2 <= capacity;
        fact ignored == observed;
        fact load_int32((owner + 1)) == capacity;
        fact load_int32(owner) == 0;
        fact *data == observed;
        fact loadable(old(owner[0..4]));
    }
    have at(statement(3).entry, owner->len) == 0 by {
        simp();
    }
    have at(statement(3).exit, owner->len) ==
        at(statement(3).entry, owner->len) + 1 by {
        simp();
    }
    apply(incremented_zero_is_one(at(statement(3).entry, load_int32(owner)), at(statement(3).exit, load_int32(owner)))) using {
        fact at(statement(3).entry, load_int32(owner)) == 0;
        fact at(statement(3).exit, load_int32(owner)) == (at(statement(3).entry, load_int32(owner)) + 1);
    }
    have owner->len == at(statement(3).exit, owner->len) by {
        simp();
    }
    have owner->len == 1 by {
        simp();
    }
    have owner->data == at(statement(3).entry, owner->data) by {
        simp();
    }
    have at(statement(3).entry, owner->data) == data by {
        simp();
    }
    apply(pointer_equality_transitive(load_int32_pointer((owner + 2)), at(statement(3).entry, load_int32_pointer((owner + 2))), data)) using {
        fact loadable(old(owner[0..4]));
        fact load_int32_pointer((owner + 2)) == at(statement(3).entry, load_int32_pointer((owner + 2)));
        fact at(statement(3).entry, load_int32_pointer((owner + 2))) == data;
    }
    apply(pointer_add_zero_equals(load_int32_pointer((owner + 2)), at(statement(3).entry, load_int32(owner)), data)) using {
        fact loadable(old(owner[0..4]));
        fact load_int32_pointer((owner + 2)) == data;
        fact at(statement(3).entry, load_int32(owner)) == 0;
    }
    have at(statement(3).exit, (owner->data)[at(statement(3).entry, owner->len)]) == first by {
        assumption();
    }
    have data[0] == first by {
        derive(data[0] == first) using {
            fact at(statement(3).exit, (owner->data)[at(statement(3).entry, owner->len)]) == first;
            fact load_int32_pointer((owner + 2)) + at(statement(3).entry, load_int32(owner)) == data;
        }
    }
    have 0 < owner->len by {
        simp();
    }
    step using {
        fact loadable(old(owner[0..4]));
        fact load_int32_pointer((owner + 2)) == data;
        fact at(statement(3).entry, load_int32(owner)) == 0;
        fact load_int32_pointer((owner + 2)) == at(statement(3).entry, load_int32_pointer((owner + 2)));
        fact at(statement(3).entry, load_int32_pointer((owner + 2))) == data;
        fact at(statement(3).exit, load_int32(owner)) == (at(statement(3).entry, load_int32(owner)) + 1);
        fact load_int32(owner) == 1;
        fact at(statement(3).entry, (load_int32(owner) + 1)) < at(statement(3).entry, load_int32((owner + 1)));
        fact 2 <= capacity;
        fact at(statement(3).entry, ignored) == observed;
        fact at(statement(3).entry, load_int32((owner + 1))) == at(statement(3).entry, capacity);
        fact at(statement(3).entry, *data) == at(statement(3).entry, observed);
        fact ignored == at(statement(3).entry, (*owner + 1));
        fact *(owner + 1) == at(statement(3).entry, *(owner + 1));
        fact *owner == at(statement(3).entry, (*owner + 1));
        fact loadable(old(data[0..capacity]));
        fact separate(memory(owner[observed..4]), memory(data[observed..capacity]));
        fact load_int32(owner) == at(statement(3).exit, load_int32(owner));
        fact data[0] == first;
        fact 0 < load_int32(owner);
    }
    have owner->len == 1 by {
        simp();
    }
    have owner->data == data by {
        simp();
    }
    apply(pointer_add_zero_equals(load_int32_pointer((owner + 2)), 0, data)) using {
        fact loadable(old(owner[0..4]));
        fact load_int32_pointer((owner + 2)) == data;
    }
    have observed == data[0] by {
        simp();
    }
    apply(int32_equality_transitive(observed, data[0], first)) using {
        fact observed == *data;
        fact *data == first;
    }
    have 1 <= owner->len by {
        simp();
    }
    step using {
        fact load_int32(owner) == 1;
        fact 2 <= capacity;
        fact observed == first;
        fact observed == data[0];
        fact *data == first;
        fact load_int32_pointer((owner + 2)) == data;
        fact at(statement(3).entry, load_int32_pointer((owner + 2))) == data;
        fact loadable(old(owner[0..4]));
        fact *owner == *owner;
        fact 0 < *owner;
        fact 1 <= load_int32(owner);
    }
    have at(statement(5).entry, owner->len) == 1 by {
        simp();
    }
    have at(statement(5).exit, owner->len) ==
        at(statement(5).entry, owner->len) - 1 by {
        simp();
    }
    apply(decremented_one_is_zero(at(statement(5).entry, load_int32(owner)), at(statement(5).exit, load_int32(owner)))) using {
        fact at(statement(5).entry, load_int32(owner)) == 1;
        fact *owner == at(statement(5).entry, (*owner - 1));
    }
    have owner->len == at(statement(5).exit, owner->len) by {
        simp();
    }
    have owner->len == 0 by {
        simp();
    }
    have observed == first by {
        simp();
    }
    execute_rest();
    simp();
}
