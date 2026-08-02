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
    execute();
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

    ensures result == owner->data[index] by auto;
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
    have index < owner->cap by simp;
    step() using {
        0 <= index;
        index < owner->len;
        index < owner->cap;
        loadable(owner->len);
        loadable(owner->cap);
        loadable(owner->data);
        0 <= owner->len;
        owner->len < owner->cap;
        terminated_at(owner->data, owner->len);
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        owner->data[owner->len] == 0;
    }
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        assumption();
    }
    have owner->data[owner->len] == 0 by {
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
    have index < index + 1 by simp;
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
    step() using {
        at(statement(0).entry, (owner->len + 1)) < at(statement(0).entry, owner->cap);
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        at(statement(0).entry, 0) <= at(statement(0).entry, owner->len);
        at(statement(0).entry, owner->len) < at(statement(0).entry, owner->cap);
        terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
    }
    step() using {
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        at(statement(0).entry, 0) <= at(statement(0).entry, owner->len);
        terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        at(statement(4).entry, (index + 1)) < at(statement(4).entry, owner->cap);
        at(statement(4).entry, index) < at(statement(4).entry, owner->cap);
        at(statement(0).entry, (owner->len + 1)) < at(statement(0).entry, owner->cap);
        at(statement(0).entry, owner->len) < at(statement(0).entry, owner->cap);
    }
    step();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        derive using {
            at(statement(2).exit, (at(statement(2).entry, owner->data) + 0)[at(statement(2).entry, index)]) == at(statement(2).entry, value);
            at(statement(3).exit, owner->len) == at(statement(3).entry, (index + 1));
            at(statement(4).exit, (at(statement(4).entry, owner->data) + 0)[at(statement(4).entry, (index + 1))]) == at(statement(4).entry, 0);
        }
    }
    have 0 <= owner->len by simp;
    have owner->len < owner->cap by {
        derive using {
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
        }
    }
    have separate(memory(object(owner)), memory(owner->data[0..owner->cap])) by {
        derive using {
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
    }
    have owner->cap == old(owner->cap) by {
        derive using {
            at(statement(3).exit, owner->len) == at(statement(3).entry, (index + 1));
        }
    }
    have owner->data == old(owner->data) by {
        derive using {
            at(statement(3).exit, owner->len) == at(statement(3).entry, (index + 1));
        }
    }
    fold(owned_string(owner));
    frame();
    have owner->len == (old(owner->len) + 1) by {
        derive using {
            at(statement(3).exit, owner->len) == at(statement(3).entry, (index + 1));
        }
    }
    have result == (old(owner->len) + 1) by {
        derive using {
            owner->len == (old(owner->len) + 1);
        }
    }
    have owner->data[old(owner->len)] == value by {
        derive using {
            owner->data == old(owner->data);
        }
    }
    have owner->data[owner->len] == 0 by {
        derive using {
            owner->len == (old(owner->len) + 1);
            owner->data == old(owner->data);
        }
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
    step() using {
        (owner->len + 1) < owner->cap;
        owner->len < owner->cap;
        1 <= owner->len;
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->len));
    }
    step() using {
        at(statement(1).entry, (owner->len + 1)) < at(statement(1).entry, owner->cap);
        at(statement(1).entry, owner->len) < at(statement(1).entry, owner->cap);
        at(statement(1).entry, 1) <= at(statement(1).entry, owner->len);
        at(statement(1).entry, loadable(old(owner->cap)));
        at(statement(1).entry, loadable(old(owner->data)));
        at(statement(1).entry, loadable(old(owner->len)));
        at(statement(0).entry, c(result)) == at(statement(0).entry, (owner->len + 1));
        owner->cap == at(statement(0).entry, owner->cap);
        owner->data == at(statement(0).entry, owner->data);
        owner->len == at(statement(0).entry, (owner->len + 1));
        owner->data[owner->len] == 0;
        at(statement(0).entry, separate(memory(owner->len), memory(owner->cap)));
        at(statement(0).entry, separate(memory(owner->len), memory(owner->data)));
        at(statement(0).entry, separate(memory(object(owner)), memory(owner->data[0..owner->cap])));
        at(statement(0).entry, separate(memory(owner->cap), memory(owner->data)));
        at(statement(0).entry, loadable(owner->data[0..owner->cap]));
        at(statement(1).entry, 0) <= at(statement(1).entry, owner->len);
        at(statement(0).entry, 0) <= at(statement(0).entry, owner->len);
    }
    have 0 == 0 by {
        normalize();
    }
    frame() using {
        (owner->len + 1) < owner->cap;
        owner->len < owner->cap;
        1 <= owner->len;
        loadable(owner->cap);
        loadable(owner->data);
        loadable(owner->len);
        at(statement(0).entry, c(result)) == at(statement(0).entry, (owner->len + 1));
        owner->cap == at(statement(0).entry, owner->cap);
        owner->data == at(statement(0).entry, owner->data);
        owner->len == at(statement(0).entry, (owner->len + 1));
        owner->data[owner->len] == 0;
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
    simp();
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
    have 0 <= owner->len - 1 by simp;
    have owner->len - 1 < owner->len by simp;
    step() using {
        1 <= owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        loadable(owner->len);
        loadable(owner->cap);
        loadable(owner->data);
        loadable(owner->data[0..owner->cap]);
        0 <= owner->len;
        owner->len < owner->cap;
        terminated_at(owner->data, owner->len);
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        0 <= (owner->len - 1);
        (owner->len - 1) < owner->len;
    }
    step() using {
        1 <= owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        0 <= owner->len;
        owner->len < owner->cap;
        terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        0 <= (owner->len - 1);
        (owner->len - 1) < owner->len;
    }
    step() using {
        1 <= owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        0 <= owner->len;
        owner->len < owner->cap;
        terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        0 <= (owner->len - 1);
        (owner->len - 1) < owner->len;
    }
    step() using {
        1 <= owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        0 <= owner->len;
        owner->len < owner->cap;
        terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        0 <= (owner->len - 1);
        (owner->len - 1) < owner->len;
    }
    step() using {
        1 <= owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        0 <= owner->len;
        owner->len < owner->cap;
        terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        0 <= (owner->len - 1);
        (owner->len - 1) < owner->len;
    }
    step() using {
        1 <= owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        0 <= owner->len;
        owner->len < owner->cap;
        terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        0 <= (owner->len - 1);
        (owner->len - 1) < owner->len;
    }
    step() using {
        at(statement(0).entry, 1) <= at(statement(0).entry, owner->len);
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(owned_string(owner), memory(owner->len));
        contains(owned_string(owner), memory(owner->cap));
        contains(owned_string(owner), memory(owner->data));
        contains(owned_string(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        at(statement(0).entry, 0) <= at(statement(0).entry, owner->len);
        at(statement(0).entry, owner->len) < at(statement(0).entry, owner->cap);
        terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        at(statement(0).entry, 0) <= at(statement(0).entry, (owner->len - 1));
        at(statement(0).entry, (owner->len - 1)) < at(statement(0).entry, owner->len);
    }
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        normalize();
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
    frame();
    have loadable(old((owner->data + (owner->len - 1))[0..1])) by {
        derive using {
            at(statement(6).exit, index) < old(owner->len);
            old(owner->len) < owner->cap;
            0 <= at(statement(6).exit, index);
            0 <= old(owner->len);
            1 <= old(owner->len);
            terminated_at(at(statement(0).entry, owner->data), at(statement(0).entry, owner->len));
            at(statement(6).entry, loadable(old(owner->data[0..owner->cap])));
            at(statement(6).entry, separate(memory(owner->len), memory(owner->cap)));
            at(statement(6).entry, separate(memory(owner->len), memory(owner->data)));
            at(statement(6).entry, separate(memory(owner->len), memory(owner->data[0..owner->cap])));
            at(statement(6).entry, separate(memory(object(owner)), memory(owner->data[0..owner->cap])));
            at(statement(6).entry, separate(memory(owner->cap), memory(owner->data)));
            at(statement(6).entry, separate(memory(owner->cap), memory(owner->data[0..owner->cap])));
            at(statement(6).entry, separate(memory(owner->data), memory(owner->data[0..owner->cap])));
            at(statement(6).entry, contains(owned_string(owner), memory(owner->len)));
            at(statement(6).entry, contains(owned_string(owner), memory(owner->cap)));
            at(statement(6).entry, contains(owned_string(owner), memory(owner->data)));
            at(statement(6).entry, contains(owned_string(owner), memory(owner->data[0..owner->cap])));
        }
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
    step() using {
        owner->len < owner->cap;
        2 <= owner->len;
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->len));
    }
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
        at(statement(0).entry, (load_int32_pointer(byte_offset(owner, 8)) + (load_int32(owner) - 1))) == at(statement(0).entry, (owner + 1));
        at(statement(0).entry, c(result)) == at(statement(0).entry, owner->cap);
        owner->cap == at(statement(0).entry, owner->cap);
        owner->data == at(statement(0).entry, owner->data);
        owner->len == at(statement(0).entry, (owner->len - 1));
        owner->data[owner->len] == 0;
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
    simp();
}

int32 owned_string_clear(struct owned_string* owner) {
    owns owned_string(owner);
    mutable owner->len, owner->data[0..1];
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->data[0] == 0;
} by {
    unfold(owned_string(owner));
    execute();
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
    consumes object(owner);
    consumes data[0..capacity];
    produces owned_string(owner);
    ensures owner->len == 0;
    ensures result == first;
} by {
    execute_until(statement(3));
    have owner->len == 0 by simp;
    have owner->cap == capacity by simp;
    have owner->len + 1 < owner->cap by simp;
    step() using {
        (owner->len + 1) < owner->cap;
        2 <= capacity;
        ignored == observed;
        owner->cap == capacity;
        owner->len == 0;
        *data == observed;
        loadable(old(object(owner)));
    }
    have at(statement(3).entry, owner->len) == 0 by simp;
    have at(statement(3).exit, owner->len) ==
        at(statement(3).entry, owner->len) + 1 by {
        simp();
    }
    apply(incremented_zero_is_one(at(statement(3).entry, owner->len), at(statement(3).exit, owner->len))) using {
        at(statement(3).entry, owner->len) == 0;
        at(statement(3).exit, owner->len) == (at(statement(3).entry, owner->len) + 1);
    }
    have owner->len == at(statement(3).exit, owner->len) by simp;
    have owner->len == 1 by simp;
    have owner->data == at(statement(3).entry, owner->data) by simp;
    have at(statement(3).entry, owner->data) == data by simp;
    apply(pointer_equality_transitive(owner->data, at(statement(3).entry, owner->data), data)) using {
        loadable(old(object(owner)));
        owner->data == at(statement(3).entry, owner->data);
        at(statement(3).entry, owner->data) == data;
    }
    apply(pointer_add_zero_equals(owner->data, at(statement(3).entry, owner->len), data)) using {
        loadable(old(object(owner)));
        owner->data == data;
        at(statement(3).entry, owner->len) == 0;
    }
    have at(statement(3).exit, owner->data[at(statement(3).entry, owner->len)]) == first by {
        assumption();
    }
    have data[0] == first by {
        derive using {
            at(statement(3).exit, owner->data[at(statement(3).entry, owner->len)]) == first;
            owner->data + at(statement(3).entry, owner->len) == data;
        }
    }
    have 0 < owner->len by simp;
    step() using {
        loadable(old(object(owner)));
        owner->data == data;
        at(statement(3).entry, owner->len) == 0;
        owner->data == at(statement(3).entry, owner->data);
        at(statement(3).entry, owner->data) == data;
        at(statement(3).exit, owner->len) == (at(statement(3).entry, owner->len) + 1);
        owner->len == 1;
        at(statement(3).entry, (owner->len + 1)) < at(statement(3).entry, owner->cap);
        2 <= capacity;
        at(statement(3).entry, ignored) == observed;
        at(statement(3).entry, owner->cap) == at(statement(3).entry, capacity);
        at(statement(3).entry, *data) == at(statement(3).entry, observed);
        ignored == at(statement(3).entry, (owner->len + 1));
        owner->cap == at(statement(3).entry, owner->cap);
        owner->len == at(statement(3).entry, (owner->len + 1));
        loadable(old(data[0..capacity]));
        separate(memory(owner[observed..4]), memory(data[observed..capacity]));
        owner->len == at(statement(3).exit, owner->len);
        data[0] == first;
        0 < owner->len;
    }
    have owner->len == 1 by simp;
    have owner->data == data by simp;
    apply(pointer_add_zero_equals(owner->data, 0, data)) using {
        loadable(old(object(owner)));
        owner->data == data;
    }
    have observed == data[0] by simp;
    apply(int32_equality_transitive(observed, data[0], first)) using {
        observed == *data;
        *data == first;
    }
    have 1 <= owner->len by simp;
    step() using {
        owner->len == 1;
        2 <= capacity;
        observed == first;
        observed == data[0];
        *data == first;
        owner->data == data;
        at(statement(3).entry, owner->data) == data;
        loadable(old(object(owner)));
        owner->len == owner->len;
        0 < owner->len;
        1 <= owner->len;
    }
    have at(statement(5).entry, owner->len) == 1 by simp;
    have at(statement(5).exit, owner->len) ==
        at(statement(5).entry, owner->len) - 1 by {
        simp();
    }
    apply(decremented_one_is_zero(at(statement(5).entry, owner->len), at(statement(5).exit, owner->len))) using {
        at(statement(5).entry, owner->len) == 1;
        owner->len == at(statement(5).entry, (owner->len - 1));
    }
    have owner->len == at(statement(5).exit, owner->len) by simp;
    have owner->len == 0 by simp;
    have observed == first by simp;
    step() using {
        owner->len == 0;
        observed == first;
    }
    simp();
}
