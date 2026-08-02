theorem incremented_zero_is_one(before: int32, after: int32) {
    requires before == 0;
    requires after == before + 1;

    ensures after == 1 by {
        rewrite(after == before + 1);
        rewrite(before == 0);
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

theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        simp();
    }
}

resource readable_input(data: int32*, length: int32) {
    views data[0..length];
    fact 0 <= length;
}

resource input_cursor(owner: struct input_cursor*) {
    owns owner->pos;
    owns owner->len;
    owns owner->data;
    views readable_input(owner->data, owner->len);
    fact 0 <= owner->pos;
    fact owner->pos <= owner->len;
    fact separate(
        memory(object(owner)),
        memory(owner->data[0..owner->len])
    );
}

verifying "input_cursor_init.c";
verifying "input_cursor_remaining.c";
verifying "input_cursor_peek.c";
verifying "input_cursor_take.c";
verifying "input_cursor_clone.c";
verifying "input_cursor_shared_pipeline.c";

int32 input_cursor_init(
    struct input_cursor* owner,
    int32 data[],
    int32 length
) {
    requires 0 <= length;
    requires separate(memory(object(owner)), memory(data[0..length]));
    consumes object(owner);
    views readable_input(data, length);
    mutable object(owner);
    produces input_cursor(owner);
    ensures result == 0;
    ensures owner->pos == 0;
    ensures owner->len == length;
    ensures owner->data == data;
} by {
    execute();
    fold(input_cursor(owner));
    frame();
    simp();
}

int32 input_cursor_remaining(struct input_cursor* owner) {
    views input_cursor(owner);
    immutable;

    ensures result == owner->len - owner->pos by auto;
}

int32 input_cursor_peek(struct input_cursor* owner) {
    requires owner->pos < owner->len;
    views input_cursor(owner);
    immutable;

    ensures result == owner->data[owner->pos];
} by {
    observe(input_cursor(owner));
    observe(readable_input(owner->data, owner->len));
    execute();
    frame();
    simp();
}

int32 input_cursor_take(struct input_cursor* owner) {
    requires owner->pos < owner->len;
    owns input_cursor(owner);
    mutable owner->pos;

    ensures result == old(owner->data[owner->pos]);
    ensures owner->pos == old(owner->pos) + 1;
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    unfold(input_cursor(owner));
    observe(readable_input(owner->data, owner->len));
    step() using {
        owner->pos < owner->len;
        separate(memory(owner->pos), memory(owner->len));
        separate(memory(owner->pos), memory(owner->data));
        separate(memory(owner->len), memory(owner->data));
        contains(input_cursor(owner), memory(owner->pos));
        contains(input_cursor(owner), memory(owner->len));
        contains(input_cursor(owner), memory(owner->data));
        loadable(owner->pos);
        loadable(owner->len);
        loadable(owner->data);
        0 <= owner->pos;
        owner->pos <= owner->len;
        separate(memory(object(owner)), memory(owner->data[0..owner->len]));
        loadable(owner->data[0..owner->len]);
        0 <= owner->len;
    }
    step() using {
        owner->pos < owner->len;
        separate(memory(owner->pos), memory(owner->len));
        separate(memory(owner->pos), memory(owner->data));
        separate(memory(owner->len), memory(owner->data));
        contains(input_cursor(owner), memory(owner->pos));
        contains(input_cursor(owner), memory(owner->len));
        contains(input_cursor(owner), memory(owner->data));
        loadable(old(owner->pos));
        loadable(old(owner->len));
        loadable(old(owner->data));
        0 <= owner->pos;
        owner->pos <= owner->len;
        separate(memory(object(owner)), memory(owner->data[0..owner->len]));
        loadable(old(owner->data[0..owner->len]));
        0 <= owner->len;
    }
    step() using {
        owner->pos < owner->len;
        separate(memory(owner->pos), memory(owner->len));
        separate(memory(owner->pos), memory(owner->data));
        separate(memory(owner->len), memory(owner->data));
        contains(input_cursor(owner), memory(owner->pos));
        contains(input_cursor(owner), memory(owner->len));
        contains(input_cursor(owner), memory(owner->data));
        loadable(old(owner->pos));
        loadable(old(owner->len));
        loadable(old(owner->data));
        0 <= owner->pos;
        owner->pos <= owner->len;
        separate(memory(object(owner)), memory(owner->data[0..owner->len]));
        loadable(old(owner->data[0..owner->len]));
        0 <= owner->len;
    }
    step();
    have 0 <= owner->pos by {
        derive using {
            at(statement(2).entry, separate(memory(owner->pos), memory(owner->len)));
            at(statement(2).entry, separate(memory(owner->pos), memory(owner->data)));
            at(statement(2).entry, separate(memory(owner->len), memory(owner->data)));
            at(statement(2).entry, contains(input_cursor(owner), memory(owner->pos)));
            at(statement(2).entry, contains(input_cursor(owner), memory(owner->len)));
            at(statement(2).entry, contains(input_cursor(owner), memory(owner->data)));
            at(statement(2).entry, loadable(old(owner->pos)));
            at(statement(2).entry, loadable(old(owner->len)));
            at(statement(2).entry, loadable(old(owner->data)));
            0 <= old(owner->pos);
            at(statement(2).entry, separate(memory(object(owner)), memory(owner->data[0..owner->len])));
            at(statement(2).entry, loadable(old(owner->data[0..owner->len])));
            old(owner->pos) < owner->len;
            old(owner->pos) <= owner->len;
            0 <= owner->len;
        }
    }
    have owner->pos <= owner->len by {
        derive using {
            old(owner->pos) < owner->len;
        }
    }
    have separate(
        memory(object(owner)),
        memory(owner->data[0..owner->len])
    ) by {
        simp();
    }
    fold(input_cursor(owner));
    frame();
    have loadable(old((load_int32_pointer(byte_offset(owner, 8)) + load_int32(owner))[0..1])) by {
        derive using {
            at(statement(2).entry, separate(memory(owner->pos), memory(owner->len)));
            at(statement(2).entry, separate(memory(owner->pos), memory(owner->data)));
            at(statement(2).entry, separate(memory(owner->len), memory(owner->data)));
            at(statement(2).entry, contains(input_cursor(owner), memory(owner->pos)));
            at(statement(2).entry, contains(input_cursor(owner), memory(owner->len)));
            at(statement(2).entry, contains(input_cursor(owner), memory(owner->data)));
            at(statement(2).entry, loadable(old(owner->pos)));
            at(statement(2).entry, loadable(old(owner->len)));
            at(statement(2).entry, loadable(old(owner->data)));
            0 <= old(owner->pos);
            at(statement(2).entry, separate(memory(object(owner)), memory(owner->data[0..owner->len])));
            at(statement(2).entry, loadable(old(owner->data[0..owner->len])));
            old(owner->pos) < owner->len;
            old(owner->pos) <= owner->len;
            0 <= owner->len;
        }
    }
    have result == old(owner->data[owner->pos]) by {
        normalize();
    }
    have owner->pos == (old(owner->pos) + 1) by {
        normalize();
    }
    have owner->len == old(owner->len) by {
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
}

int32 input_cursor_clone(
    struct input_cursor* target,
    struct input_cursor* source
) {
    requires separate(memory(object(target)), memory(object(source)));
    requires separate(
        memory(object(target)),
        memory(source->data[0..source->len])
    );
    consumes object(target);
    views input_cursor(source);
    mutable object(target);
    produces input_cursor(target);
    ensures result == source->pos;
    ensures target->pos == source->pos;
    ensures target->len == source->len;
    ensures target->data == source->data;
} by {
    observe(input_cursor(source));
    step();
    step();
    step() using {
        at(statement(0).entry, separate(memory(object(target)), memory(object(source))));
        at(statement(0).entry, separate(memory(object(target)), memory(source->data[0..source->len])));
        at(statement(0).entry, loadable(target[0..4]));
        at(statement(0).entry, separate(memory(source->pos), memory(source->len)));
        at(statement(0).entry, separate(memory(source->pos), memory(source->data)));
        at(statement(0).entry, separate(memory(source->len), memory(source->data)));
        at(statement(0).entry, contains(input_cursor(source), memory(source->pos)));
        at(statement(0).entry, contains(input_cursor(source), memory(source->len)));
        at(statement(0).entry, contains(input_cursor(source), memory(source->data)));
        at(statement(0).entry, loadable(source->pos));
        at(statement(0).entry, loadable(source->len));
        at(statement(0).entry, loadable(source->data));
        at(statement(0).entry, separate(memory(object(source)), memory(source->data[0..source->len])));
        at(statement(0).entry, loadable(source->data[0..source->len]));
        0 <= source->pos;
        source->pos <= source->len;
        0 <= source->len;
        at(statement(1).entry, 0) <= at(statement(1).entry, source->pos);
        at(statement(1).entry, source->pos) <= at(statement(1).entry, source->len);
        at(statement(1).entry, 0) <= at(statement(1).entry, source->len);
    }
    step() using {
        separate(memory(object(target)), memory(object(source)));
        separate(memory(object(target)), memory(source->data[0..source->len]));
        loadable(old(object(target)));
        loadable(old(source->pos));
        loadable(old(source->len));
        loadable(old(source->data));
    }
    fold(input_cursor(target));
    frame();
    simp();
}

int32 input_cursor_shared_pipeline(
    struct input_cursor* left,
    struct input_cursor* right,
    int32 data[],
    int32 length
) {
    requires 1 <= length;
    requires separate(memory(object(left)), memory(data[0..length]));
    requires separate(memory(object(right)), memory(data[0..length]));
    consumes object(left);
    consumes object(right);
    views readable_input(data, length);
    mutable object(left), object(right);
    produces input_cursor(left);
    produces input_cursor(right);
    ensures left->pos == 1;
    ensures right->pos == 0;
    ensures result == data[0];
} by {
    execute_until(statement(4));
    have separate(memory(object(right)), memory(left->data[0..left->len])) by {
        derive using {
            left->len == length;
            left->data == data;
            separate(memory(object(right)), memory(data[0..length]));
        }
    }
    have left->pos < left->len by {
        derive using {
            1 <= length;
            left->len == length;
            left->pos == left_value;
        }
    }
    have left->pos == 0 by simp;
    have left->data == data by simp;
    step() using {
        left->pos < left->len;
        1 <= length;
        left->pos == 0;
        left->len == length;
        left->data == data;
        loadable(old(object(left)));
        loadable(old(object(right)));
        separate(memory(object(left)), memory(object(right)));
        separate(memory(object(left)), memory(data[0..length]));
        separate(memory(object(right)), memory(left->data[0..left->len]));
    }
    transport(at(statement(4).entry, left->pos) < at(statement(4).entry, left->len), left->pos < left->len) using {
        at(statement(4).entry, left->pos) < at(statement(4).entry, left->len);
    }
    have right->pos < right->len by {
        derive using {
            left->pos < left->len;
            right->len == left->len;
            right->pos == left->pos;
        }
    }
    have right->pos == 0 by {
        derive using {
            left->pos == left_value;
            right->pos == left->pos;
        }
    }
    have right->data == left->data by simp;
    have left->data == data by simp;
    apply(pointer_equality_transitive(right->data, left->data, data));
    step() using {
        loadable(old(object(left)));
        loadable(old(object(right)));
        right->data == left->data;
        left->data == data;
        right->data == data;
        1 <= length;
        separate(memory(object(left)), memory(object(right)));
        separate(memory(object(left)), memory(data[0..length]));
        ignored == left->pos;
        right->pos == left->pos;
        right->len == left->len;
        left->pos < left->len;
        left->pos == left_value;
        left->len == length;
        separate(memory(object(right)), memory(data[0..length]));
        separate(memory(left[left_value..4]), memory(right[left_value..4]));
        loadable(old(data[0..length]));
        0 <= length;
        at(statement(4).entry, left->pos) == at(statement(4).entry, 0);
        at(statement(4).entry, left->len) == at(statement(4).entry, length);
        at(statement(4).entry, left->data) == at(statement(4).entry, data);
        at(statement(4).entry, left->pos) < at(statement(4).entry, left->len);
        right->pos < right->len;
        right->pos == 0;
    }
    have left->len == left->len by {
        normalize();
    }
    have left->data == left->data by {
        normalize();
    }
    transport(at(statement(5).entry, right->data) == at(statement(5).entry, left->data), right->data == left->data) using {
        at(statement(5).entry, right->data) == at(statement(5).entry, left->data);
    }
    transport(at(statement(5).entry, left->data) == data, left->data == data) using {
        at(statement(5).entry, left->data) == data;
    }
    transport(at(statement(5).entry, right->data) == data, right->data == data) using {
        at(statement(5).entry, right->data) == data;
    }
    transport(at(statement(5).entry, right->pos) == at(statement(5).entry, left->pos), right->pos == at(statement(5).entry, left->pos)) using {
        at(statement(5).entry, right->pos) == at(statement(5).entry, left->pos);
    }
    transport(at(statement(5).entry, right->len) == at(statement(5).entry, left->len), right->len == left->len) using {
        at(statement(5).entry, right->len) == at(statement(5).entry, left->len);
    }
    transport(at(statement(5).entry, left->pos) < at(statement(5).entry, left->len), at(statement(5).entry, left->pos) < left->len) using {
        at(statement(5).entry, left->pos) < at(statement(5).entry, left->len);
    }
    transport(at(statement(5).entry, left->len) == length, left->len == length) using {
        at(statement(5).entry, left->len) == length;
    }
    transport(at(statement(5).entry, right->pos) < at(statement(5).entry, right->len), right->pos < right->len) using {
        at(statement(5).entry, right->pos) < at(statement(5).entry, right->len);
    }
    transport(at(statement(5).entry, right->pos) == 0, right->pos == 0) using {
        at(statement(5).entry, right->pos) == 0;
    }
    have at(statement(5).entry, left->pos) == 0 by simp;
    have left->pos == at(statement(5).entry, left->pos) + 1 by simp;
    apply(incremented_zero_is_one(
        at(statement(5).entry, left->pos),
        left->pos
    ));
    step() using {
        right->pos < right->len;
        1 <= length;
        right->len == left->len;
        left->pos == 1;
        left->pos == (at(statement(5).entry, left->pos) + 1);
        right->pos == right_value;
        at(statement(5).entry, left->pos) == 0;
        loadable(old(object(left)));
        loadable(old(object(right)));
        separate(memory(object(left)), memory(data[0..length]));
        separate(memory(object(right)), memory(data[0..length]));
        right_value <= length;
        left->len == left->len;
    }
    have right->pos == 0 by simp;
    have right->data == data by simp;
    have right_value == right->data[right->pos] by simp;
    have right->data[right->pos] == data[0] by {
        derive using {
            right->pos == 0;
            right->data == data;
        }
    }
    apply(int32_equality_transitive(right_value, right->data[right->pos], data[0])) using {
        loadable(old(object(right)));
        right_value == right->data[right->pos];
        right->data[right->pos] == data[0];
    }
    step() using {
        at(statement(6).entry, loadable(old(object(right))));
        right_value == right->data[right->pos];
        right->data[right->pos] == data[0];
        right_value == *data;
        at(statement(6).entry, 1) <= at(statement(6).entry, length);
        at(statement(5).entry, left->pos) == 0;
        at(statement(6).entry, loadable(old(object(left))));
        at(statement(6).entry, separate(memory(object(left)), memory(data[0..length])));
        at(statement(6).entry, separate(memory(object(right)), memory(data[0..length])));
        at(statement(6).entry, right_value) <= at(statement(6).entry, length);
        right->pos < right->len;
        right->len == left->len;
        left->pos == 1;
        left->pos == at(statement(5).entry, (left->pos + 1));
        right->pos == 0;
        left->len == left->len;
        at(statement(6).entry, left->pos) == at(statement(6).entry, (at(statement(5).entry, left->pos) + 1));
        at(statement(5).entry, separate(memory(left[left_value..4]), memory(right[left_value..4])));
        at(statement(5).entry, ignored) == at(statement(5).entry, left->pos);
        at(statement(4).entry, left->len) == at(statement(4).entry, length);
        at(statement(5).entry, loadable(old(data[0..length])));
        at(statement(4).entry, left->pos) == at(statement(4).entry, 0);
        at(statement(4).entry, left->data) == at(statement(4).entry, data);
        at(statement(4).entry, left->pos) < at(statement(4).entry, left->len);
        left_value == at(statement(5).entry, left->data[left->pos]);
        left->len == at(statement(5).entry, left->len);
        left->data == at(statement(5).entry, left->data);
        right->data == left->data;
        left->data == data;
        right->data == data;
        right->pos == at(statement(5).entry, left->pos);
        at(statement(6).entry, right->len) == at(statement(6).entry, left->len);
        at(statement(5).entry, left->pos) < left->len;
        at(statement(6).entry, right->pos) < at(statement(6).entry, right->len);
        at(statement(6).entry, right->pos) == at(statement(6).entry, right_value);
        at(statement(5).entry, right->data) == at(statement(5).entry, left->data);
        at(statement(5).entry, left->data) == data;
        at(statement(5).entry, right->data) == data;
        at(statement(4).entry, separate(memory(object(right)), memory(left->data[0..left->len])));
        at(statement(5).entry, right->pos) == at(statement(5).entry, left->pos);
        at(statement(5).entry, right->len) == at(statement(5).entry, left->len);
        at(statement(5).entry, left->pos) < at(statement(5).entry, left->len);
        at(statement(5).entry, left->len) == length;
        at(statement(5).entry, right->pos) < at(statement(5).entry, right->len);
        at(statement(5).entry, right->pos) == 0;
        at(statement(6).entry, left->len) == at(statement(6).entry, left->len);
        left->data == left->data;
        left->len == length;
    }
    frame() using {
        loadable(right[0..4]);
        right_value == right->data[right->pos];
        right->data[right->pos] == data[0];
        right_value == *data;
        1 <= length;
        left->pos == left_value;
        loadable(left[0..4]);
        separate(memory(object(left)), memory(data[0..length]));
        separate(memory(object(right)), memory(data[0..length]));
        0 <= length;
        at(statement(7).entry, left->pos) == at(statement(7).entry, 1);
        left->pos == at(statement(5).entry, (left->pos + 1));
        left->len == left->len;
        left->pos == (at(statement(5).entry, left->pos) + 1);
        separate(memory(object(left)), memory(object(right)));
        ignored == left->pos;
        at(statement(4).entry, left->len) == at(statement(4).entry, length);
        loadable(data[0..length]);
        left->pos == 0;
        at(statement(4).entry, left->data) == at(statement(4).entry, data);
        at(statement(4).entry, left->pos) < at(statement(4).entry, left->len);
        left_value == at(statement(5).entry, left->data[left->pos]);
        left->len == at(statement(5).entry, left->len);
        left->data == at(statement(5).entry, left->data);
        right->pos == at(statement(5).entry, left->pos);
        at(statement(6).entry, right->len) == at(statement(6).entry, left->len);
        at(statement(5).entry, left->pos) < left->len;
        at(statement(6).entry, right->pos) < at(statement(6).entry, right->len);
        right->pos == right_value;
        at(statement(5).entry, right->data) == at(statement(5).entry, left->data);
        at(statement(5).entry, left->data) == data;
        at(statement(5).entry, right->data) == at(statement(5).entry, data);
        separate(memory(object(right)), memory(left->data[0..left->len]));
        right->pos == left->pos;
        at(statement(5).entry, right->len) == at(statement(5).entry, left->len);
        at(statement(5).entry, left->len) == length;
        at(statement(5).entry, right->pos) < at(statement(5).entry, right->len);
        at(statement(5).entry, right->pos) == at(statement(5).entry, 0);
        left->data == left->data;
        at(statement(7).entry, left->data) == at(statement(7).entry, left->data);
    }
    simp();
}
