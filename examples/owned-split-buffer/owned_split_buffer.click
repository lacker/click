theorem incremented_one_is_two(before: int32, after: int32) {
    requires before == 1;
    requires after == before + 1;

    ensures after == 2 by {
        rewrite(after == before + 1);
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

resource owned_split_buffer(owner: struct owned_split_buffer*) {
    owns owner->split;
    owns owner->len;
    owns owner->data;
    owns owner->data[0..owner->split];
    owns owner->data[owner->split..owner->len];
    fact 0 <= owner->split;
    fact owner->split <= owner->len;
    fact separate(
        memory(object(owner)),
        memory(owner->data[0..owner->len])
    );
}

verifying "owned_split_buffer_init.c";
verifying "owned_split_buffer_set_left.c";
verifying "owned_split_buffer_set_right.c";
verifying "owned_split_buffer_move_right.c";
verifying "owned_split_buffer_get_left.c";
verifying "owned_split_buffer_pipeline.c";

int32 owned_split_buffer_init(
    struct owned_split_buffer* owner,
    int32 data[],
    int32 length,
    int32 split
) {
    requires 0 <= split;
    requires split <= length;
    consumes object(owner);
    consumes data[0..length];
    mutable object(owner);
    produces owned_split_buffer(owner);
    ensures result == split;
    ensures owner->split == split;
    ensures owner->len == length;
    ensures owner->data == data;
} by {
    execute();
    fold(owned_split_buffer(owner));
    frame();
    simp();
}

int32 owned_split_buffer_set_left(
    struct owned_split_buffer* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->split;
    owns owned_split_buffer(owner);
    mutable owner->data[index..index + 1];
    ensures result == value;
    ensures owner->data[index] == value;
    ensures owner->split == old(owner->split);
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    unfold(owned_split_buffer(owner));
    execute();
    fold(owned_split_buffer(owner));
    have index < index + 1 by simp;
    frame();
    simp();
}

int32 owned_split_buffer_set_right(
    struct owned_split_buffer* owner,
    int32 index,
    int32 value
) {
    requires owner->split <= index;
    requires index < owner->len;
    owns owned_split_buffer(owner);
    mutable owner->data[index..index + 1];
    ensures result == value;
    ensures owner->data[index] == value;
    ensures owner->split == old(owner->split);
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    unfold(owned_split_buffer(owner));
    step() using {
        owner->split <= index;
        index < owner->len;
        loadable(owner->split);
        loadable(owner->len);
        loadable(owner->data);
        0 <= owner->split;
        owner->split <= owner->len;
        separate(memory(object(owner)), memory(owner->data[0..owner->len]));
    }
    step() using {
        owner->split <= index;
        index < owner->len;
        loadable(old(owner->split));
        loadable(old(owner->len));
        loadable(old(owner->data));
        0 <= owner->split;
        owner->split <= owner->len;
        separate(memory(object(owner)), memory(owner->data[0..owner->len]));
    }
    fold(owned_split_buffer(owner));
    have index < index + 1 by simp;
    frame();
    simp();
}

int32 owned_split_buffer_move_right(struct owned_split_buffer* owner) {
    requires owner->split < owner->len;
    owns owned_split_buffer(owner);
    mutable owner->split;
    ensures result == old(owner->split) + 1;
    ensures owner->split == old(owner->split) + 1;
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    unfold(owned_split_buffer(owner));
    step();
    step();
    have 0 <= owner->split by simp;
    have owner->split <= owner->len by simp;
    have separate(
        memory(object(owner)),
        memory(owner->data[0..owner->len])
    ) by {
        simp();
    }
    fold(owned_split_buffer(owner));
    frame();
    simp();
}

int32 owned_split_buffer_get_left(
    struct owned_split_buffer* owner,
    int32 index
) {
    requires 0 <= index;
    requires index < owner->split;
    views owned_split_buffer(owner);
    immutable;
    ensures result == owner->data[index] by auto;
}

int32 owned_split_buffer_pipeline(
    struct owned_split_buffer* owner,
    int32 data[],
    int32 length,
    int32 left_value,
    int32 right_value
) {
    requires 2 <= length;
    consumes object(owner);
    consumes data[0..length];
    produces owned_split_buffer(owner);
    ensures owner->split == 2;
    ensures owner->len == length;
    ensures owner->data == data;
    ensures data[0] == left_value;
    ensures data[1] == right_value;
    ensures result == right_value;
} by {
    step();
    step();
    step() using {
        2 <= length;
        loadable(old(object(owner)));
        loadable(old(data[0..length]));
        separate(memory(owner[0..4]), memory(data[0..length]));
    }
    step() using {
        2 <= length;
        loadable(old(object(owner)));
        loadable(old(data[0..length]));
        separate(memory(owner[0..4]), memory(data[0..length]));
        ignored == 1;
        owner->split == 1;
        owner->len == length;
        owner->data == data;
    }
    have owner->split == owner->split by {
        normalize();
    }
    have owner->len == owner->len by {
        normalize();
    }
    have owner->data == owner->data by {
        normalize();
    }
    transport(at(statement(3).entry, owner->split) == 1, owner->split == 1) using {
        at(statement(3).entry, owner->split) == 1;
        2 <= length;
        at(statement(3).entry, owner->data) == data;
    }
    transport(at(statement(3).entry, owner->len) == length, owner->len == length) using {
        at(statement(3).entry, owner->len) == length;
        2 <= length;
        at(statement(3).entry, owner->data) == data;
    }
    transport(at(statement(3).entry, owner->data) == data, owner->data == data) using {
        at(statement(3).entry, owner->data) == data;
        2 <= length;
    }
    have owner->data == data by simp;
    have data[0] == left_value by {
        simp() using {
            at(statement(4).entry, owner->data[0]) == at(statement(4).entry, left_value);
            owner->data == data;
        }
    }
    have 1 < length by {
        simp() using {
            2 <= length;
        }
    }
    have 1 < owner->len by {
        rewrite(owner->len == length);
        assumption();
    }
    step() using {
        1 < owner->len;
        2 <= length;
        ignored == left_value;
        owner->len == length;
        owner->split == 1;
        data[0] == left_value;
        owner->data == data;
        loadable(old(object(owner)));
        owner->split == owner->split;
        owner->len == owner->len;
        separate(memory(object(owner)), memory(data[0..length]));
    }
    transport(at(statement(4).entry, owner->data) == data, owner->data == data) using {
        at(statement(4).entry, owner->data) == data;
        2 <= length;
    }
    transport(at(statement(4).entry, 1) < at(statement(4).entry, owner->len), 1 < owner->len) using {
        at(statement(4).entry, 1) < at(statement(4).entry, owner->len);
        owner->data == data;
        separate(memory(object(owner)), memory(data[0..length]));
        2 <= length;
    }
    have data[0] == left_value by {
        assumption();
    }
    have data[1] == right_value by {
        simp() using {
            at(statement(5).entry, *(owner->data + 1)) == at(statement(5).entry, right_value);
            owner->data == data;
        }
    }
    have owner->split < owner->len by {
        rewrite(owner->split == 1);
        assumption();
    }
    step() using {
        owner->split < owner->len;
        2 <= length;
        loadable(object(owner));
        owner->len == length;
        owner->data == data;
        data[0] == left_value;
        data[1] == right_value;
        separate(memory(object(owner)), memory(data[0..length]));
    }
    have owner->data == data by {
        simp() using {
            owner->data == at(statement(4).entry, owner->data);
            at(statement(4).entry, owner->data) == at(statement(3).entry, owner->data);
            at(statement(3).entry, owner->data) == at(statement(3).entry, data);
        }
    }
    have data[0] == left_value by {
        assumption();
    }
    have data[1] == right_value by {
        assumption();
    }
    have at(statement(5).entry, owner->split) == 1 by simp;
    have at(statement(5).exit, owner->split) ==
        at(statement(5).entry, owner->split) + 1 by {
        simp();
    }
    apply(incremented_one_is_two(
        at(statement(5).entry, owner->split),
        at(statement(5).exit, owner->split)
    ));
    have owner->split == 2 by simp;
    have 1 < owner->split by simp;
    have owner->len == length by simp;
    have owner->data == data by simp;
    have data[0] == left_value by simp;
    have data[1] == right_value by simp;
    step() using {
        1 < owner->split;
        loadable(object(owner));
        owner->split == 2;
        owner->len == length;
        owner->data == data;
        data[0] == left_value;
        data[1] == right_value;
    }
    have owner->split == 2 by simp;
    have owner->len == length by simp;
    have owner->data == data by simp;
    have data[0] == left_value by simp;
    have data[1] == right_value by simp;
    have c(result) == data[1] by {
        simp() using {
            at(statement(7).entry, c(result)) == at(statement(7).entry, *(owner->data + 1));
            owner->data == data;
        }
    }
    apply(int32_equality_transitive(
        c(result),
        data[1],
        right_value
    ));
    step() using {
        c(result) == data[1];
        data[1] == right_value;
        c(result) == right_value;
        at(statement(4).entry, loadable(old(object(owner))));
        1 < owner->split;
        owner->split == 2;
        owner->len == length;
        owner->data == data;
        data[0] == left_value;
        at(statement(5).entry, owner->split) == 1;
        at(statement(5).exit, owner->split) == (at(statement(5).entry, owner->split) + 1);
        at(statement(5).entry, 2) <= at(statement(5).entry, length);
        at(statement(5).entry, separate(memory(object(owner)), memory(data[0..length])));
        ignored == at(statement(5).entry, (owner->split + 1));
        owner->len == at(statement(5).entry, owner->len);
        owner->data == at(statement(5).entry, owner->data);
        owner->split == at(statement(5).entry, (owner->split + 1));
        at(statement(5).entry, owner->split) < owner->len;
        at(statement(6).entry, owner->len) == at(statement(6).entry, length);
        at(statement(6).entry, owner->data) == at(statement(6).entry, data);
        at(statement(6).entry, data[0]) == at(statement(6).entry, left_value);
        at(statement(6).entry, data[1]) == at(statement(6).entry, right_value);
        at(statement(4).entry, ignored) == at(statement(4).entry, left_value);
        at(statement(5).entry, owner->split) == at(statement(4).entry, owner->split);
        at(statement(5).entry, owner->len) == at(statement(4).entry, owner->len);
        at(statement(5).entry, owner->data) == at(statement(4).entry, owner->data);
        at(statement(5).entry, 1) < at(statement(5).entry, owner->len);
        at(statement(5).entry, owner->len) == at(statement(5).entry, length);
        at(statement(5).entry, data[0]) == at(statement(5).entry, left_value);
        at(statement(5).entry, owner->data) == at(statement(5).entry, data);
        at(statement(5).entry, owner->split) == at(statement(5).entry, owner->split);
        at(statement(5).entry, owner->len) == at(statement(5).entry, owner->len);
        at(statement(3).entry, loadable(old(data[0..length])));
        at(statement(3).entry, ignored) == at(statement(3).entry, 1);
        at(statement(4).entry, owner->split) == at(statement(3).entry, owner->split);
        at(statement(4).entry, owner->len) == at(statement(3).entry, owner->len);
        at(statement(4).entry, owner->data) == at(statement(3).entry, owner->data);
        at(statement(4).entry, owner->data[0]) == at(statement(4).entry, left_value);
        at(statement(4).entry, owner->split) == at(statement(4).entry, 1);
        at(statement(4).entry, owner->len) == at(statement(4).entry, length);
        at(statement(4).entry, owner->data) == data;
        at(statement(3).entry, owner->split) == 1;
        at(statement(3).entry, owner->len) == length;
        at(statement(3).entry, owner->data) == data;
        at(statement(4).entry, owner->split) == at(statement(4).entry, owner->split);
        at(statement(4).entry, owner->len) == at(statement(4).entry, owner->len);
        owner->data == owner->data;
        at(statement(4).entry, data[0]) == at(statement(4).entry, left_value);
        at(statement(4).entry, 1) < at(statement(4).entry, owner->len);
        at(statement(5).entry, data[1]) == at(statement(5).entry, right_value);
        at(statement(5).entry, owner->split) < at(statement(5).entry, owner->len);
        at(statement(6).entry, owner->split) == at(statement(6).entry, 2);
        at(statement(6).entry, 1) < at(statement(6).entry, owner->split);
    }
    simp();
}
