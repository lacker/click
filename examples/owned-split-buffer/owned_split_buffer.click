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
    owns (owner->data)[0..owner->split];
    owns (owner->data)[owner->split..owner->len];
    fact 0 <= owner->split;
    fact owner->split <= owner->len;
    fact separate(
        memory(object(owner)),
        memory((owner->data)[0..owner->len])
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
    execute_rest();
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
    mutable (owner->data)[index..index + 1];
    ensures result == value;
    ensures (owner->data)[index] == value;
    ensures owner->split == old(owner->split);
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    unfold(owned_split_buffer(owner));
    execute_rest();
    fold(owned_split_buffer(owner));
    have index < index + 1 by { simp(); }
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
    mutable (owner->data)[index..index + 1];
    ensures result == value;
    ensures (owner->data)[index] == value;
    ensures owner->split == old(owner->split);
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    unfold(owned_split_buffer(owner));
    step using {
        fact owner->split <= index;
        fact index < owner->len;
        fact loadable(owner->split);
        fact loadable(owner->len);
        fact loadable(owner->data);
        fact 0 <= owner->split;
        fact owner->split <= owner->len;
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->len]));
    }
    step using {
        fact owner->split <= index;
        fact index < owner->len;
        fact loadable(old(owner->split));
        fact loadable(old(owner->len));
        fact loadable(old(owner->data));
        fact 0 <= owner->split;
        fact owner->split <= owner->len;
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->len]));
    }
    fold(owned_split_buffer(owner));
    have index < index + 1 by { simp(); }
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
    execute_step();
    execute_step();
    have 0 <= owner->split by { simp(); }
    have owner->split <= owner->len by { simp(); }
    have separate(
        memory(object(owner)),
        memory((owner->data)[0..owner->len])
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
    ensures result == (owner->data)[index] by auto;
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
    step using {
        fact 2 <= length;
        fact loadable(object(owner));
        fact loadable(data[0..length]);
        fact separate(memory(object(owner)), memory(data[0..length]));
    }
    step using {
        fact 2 <= length;
        fact loadable(old(object(owner)));
        fact loadable(old(data[0..length]));
        fact separate(memory(owner[ignored..4]), memory(data[ignored..length]));
    }
    step using {
        fact 2 <= length;
        fact loadable(old(object(owner)));
        fact loadable(old(data[0..length]));
        fact separate(memory(owner[ignored..4]), memory(data[ignored..length]));
    }
    step using {
        fact 2 <= length;
        fact loadable(old(object(owner)));
        fact loadable(old(data[0..length]));
        fact separate(memory(owner[read_value..4]), memory(data[read_value..length]));
        fact ignored == 1;
        fact owner->split == 1;
        fact owner->len == length;
        fact owner->data == data;
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
        fact at(statement(3).entry, owner->split) == 1;
        fact 2 <= length;
        fact at(statement(3).entry, owner->data) == data;
    }
    transport(at(statement(3).entry, owner->len) == length, owner->len == length) using {
        fact at(statement(3).entry, owner->len) == length;
        fact 2 <= length;
        fact at(statement(3).entry, owner->data) == data;
    }
    transport(at(statement(3).entry, owner->data) == data, owner->data == data) using {
        fact at(statement(3).entry, owner->data) == data;
        fact 2 <= length;
    }
    have owner->data == data by {
        simp();
    }
    have data[0] == left_value by {
        derive(data[0] == left_value) using {
            fact at(statement(4).entry, (owner->data)[0]) == at(statement(4).entry, left_value);
            fact owner->data == data;
        }
    }
    have 1 < owner->len by {
        calculate(1 < owner->len) using {
            fact 2 <= length;
            fact ignored == left_value;
            fact owner->len == length;
            fact owner->len == owner->len;
            fact owner->split == 1;
            fact owner->split == owner->split;
            fact data[0] == left_value;
            fact owner->data == data;
            fact loadable(old(object(owner)));
        }
    }
    step using {
        fact 1 < owner->len;
        fact 2 <= length;
        fact ignored == left_value;
        fact owner->len == length;
        fact owner->split == 1;
        fact data[0] == left_value;
        fact owner->data == data;
        fact loadable(old(object(owner)));
        fact owner->split == owner->split;
        fact owner->len == owner->len;
        fact separate(memory(object(owner)), memory(data[0..length]));
    }
    transport(at(statement(4).entry, owner->data) == data, owner->data == data) using {
        fact at(statement(4).entry, owner->data) == data;
        fact 2 <= length;
    }
    transport(at(statement(4).entry, 1) < at(statement(4).entry, owner->len), 1 < owner->len) using {
        fact at(statement(4).entry, 1) < at(statement(4).entry, owner->len);
        fact owner->data == data;
        fact separate(memory(object(owner)), memory(data[0..length]));
        fact 2 <= length;
    }
    have data[0] == left_value by {
        assumption();
    }
    have data[1] == right_value by {
        derive(data[1] == right_value) using {
            fact at(statement(5).entry, *(owner->data + 1)) == at(statement(5).entry, right_value);
            fact owner->data == data;
        }
    }
    have owner->split < owner->len by {
        derive(owner->split < owner->len) using {
            fact 1 < owner->len;
            fact owner->split == 1;
        }
    }
    step using {
        fact owner->split < owner->len;
        fact 2 <= length;
        fact loadable(object(owner));
        fact owner->len == length;
        fact owner->data == data;
        fact data[0] == left_value;
        fact data[1] == right_value;
        fact separate(memory(object(owner)), memory(data[0..length]));
    }
    have owner->data == data by {
        derive(owner->data == data) using {
            fact owner->data == at(statement(4).entry, owner->data);
            fact at(statement(4).entry, owner->data) == at(statement(3).entry, owner->data);
            fact at(statement(3).entry, owner->data) == at(statement(3).entry, data);
        }
    }
    have data[0] == left_value by {
        assumption();
    }
    have data[1] == right_value by {
        assumption();
    }
    have at(statement(5).entry, owner->split) == 1 by {
        simp();
    }
    have at(statement(5).exit, owner->split) ==
        at(statement(5).entry, owner->split) + 1 by {
        simp();
    }
    apply(incremented_one_is_two(
        at(statement(5).entry, owner->split),
        at(statement(5).exit, owner->split)
    ));
    have owner->split == 2 by {
        simp();
    }
    have 1 < owner->split by {
        simp();
    }
    have owner->len == length by {
        simp();
    }
    have owner->data == data by {
        simp();
    }
    have data[0] == left_value by {
        simp();
    }
    have data[1] == right_value by {
        simp();
    }
    step using {
        fact 1 < owner->split;
        fact loadable(object(owner));
        fact owner->split == 2;
        fact owner->len == length;
        fact owner->data == data;
        fact data[0] == left_value;
        fact data[1] == right_value;
    }
    have owner->split == 2 by {
        simp();
    }
    have owner->len == length by {
        simp();
    }
    have owner->data == data by {
        simp();
    }
    have data[0] == left_value by {
        simp();
    }
    have data[1] == right_value by {
        simp();
    }
    have read_value == data[1] by {
        derive(read_value == data[1]) using {
            fact at(statement(7).entry, read_value) == at(statement(7).entry, *(owner->data + 1));
            fact owner->data == data;
        }
    }
    apply(int32_equality_transitive(
        read_value,
        data[1],
        right_value
    ));
    step using {
        fact read_value == data[1];
        fact data[1] == right_value;
        fact read_value == right_value;
        fact at(statement(4).entry, loadable(old(object(owner))));
        fact 1 < owner->split;
        fact owner->split == 2;
        fact owner->len == length;
        fact owner->data == data;
        fact data[0] == left_value;
        fact at(statement(5).entry, owner->split) == 1;
        fact at(statement(5).exit, owner->split) == (at(statement(5).entry, owner->split) + 1);
        fact at(statement(5).entry, 2) <= at(statement(5).entry, length);
        fact at(statement(5).entry, separate(memory(object(owner)), memory(data[0..length])));
        fact ignored == at(statement(5).entry, (owner->split + 1));
        fact owner->len == at(statement(5).entry, owner->len);
        fact owner->data == at(statement(5).entry, owner->data);
        fact owner->split == at(statement(5).entry, (owner->split + 1));
        fact at(statement(5).entry, owner->split) < owner->len;
        fact at(statement(6).entry, owner->len) == at(statement(6).entry, length);
        fact at(statement(6).entry, owner->data) == at(statement(6).entry, data);
        fact at(statement(6).entry, data[0]) == at(statement(6).entry, left_value);
        fact at(statement(6).entry, data[1]) == at(statement(6).entry, right_value);
        fact at(statement(4).entry, ignored) == at(statement(4).entry, left_value);
        fact at(statement(5).entry, owner->split) == at(statement(4).entry, owner->split);
        fact at(statement(5).entry, owner->len) == at(statement(4).entry, owner->len);
        fact at(statement(5).entry, owner->data) == at(statement(4).entry, owner->data);
        fact at(statement(5).entry, 1) < at(statement(5).entry, owner->len);
        fact at(statement(5).entry, owner->len) == at(statement(5).entry, length);
        fact at(statement(5).entry, data[0]) == at(statement(5).entry, left_value);
        fact at(statement(5).entry, owner->data) == at(statement(5).entry, data);
        fact at(statement(5).entry, owner->split) == at(statement(5).entry, owner->split);
        fact at(statement(5).entry, owner->len) == at(statement(5).entry, owner->len);
        fact at(statement(3).entry, loadable(old(data[0..length])));
        fact at(statement(3).entry, ignored) == at(statement(3).entry, 1);
        fact at(statement(4).entry, owner->split) == at(statement(3).entry, owner->split);
        fact at(statement(4).entry, owner->len) == at(statement(3).entry, owner->len);
        fact at(statement(4).entry, owner->data) == at(statement(3).entry, owner->data);
        fact at(statement(4).entry, owner->data[0]) == at(statement(4).entry, left_value);
        fact at(statement(4).entry, owner->split) == at(statement(4).entry, 1);
        fact at(statement(4).entry, owner->len) == at(statement(4).entry, length);
        fact at(statement(4).entry, owner->data) == data;
        fact at(statement(3).entry, owner->split) == 1;
        fact at(statement(3).entry, owner->len) == length;
        fact at(statement(3).entry, owner->data) == data;
        fact at(statement(4).entry, owner->split) == at(statement(4).entry, owner->split);
        fact at(statement(4).entry, owner->len) == at(statement(4).entry, owner->len);
        fact owner->data == owner->data;
        fact at(statement(4).entry, data[0]) == at(statement(4).entry, left_value);
        fact at(statement(4).entry, 1) < at(statement(4).entry, owner->len);
        fact at(statement(5).entry, data[1]) == at(statement(5).entry, right_value);
        fact at(statement(5).entry, owner->split) < at(statement(5).entry, owner->len);
        fact at(statement(6).entry, owner->split) == at(statement(6).entry, 2);
        fact at(statement(6).entry, 1) < at(statement(6).entry, owner->split);
    }
    simp();
}
