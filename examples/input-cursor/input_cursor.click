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
        memory((owner->data)[0..owner->len])
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
    execute_rest();
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

    ensures result == (owner->data)[owner->pos];
} by {
    observe(input_cursor(owner));
    observe(readable_input(owner->data, owner->len));
    execute_rest();
    frame();
    simp();
}

int32 input_cursor_take(struct input_cursor* owner) {
    requires owner->pos < owner->len;
    owns input_cursor(owner);
    mutable_field(owner->pos);

    ensures result == old((owner->data)[owner->pos]);
    ensures owner->pos == old(owner->pos) + 1;
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    unfold(input_cursor(owner));
    observe(readable_input(owner->data, owner->len));
    step using {
        fact owner->pos < owner->len;
        fact separate(memory(owner->pos), memory(owner->len));
        fact separate(memory(owner->pos), memory(owner->data));
        fact separate(memory(owner->len), memory(owner->data));
        fact contains(input_cursor(owner), memory(owner->pos));
        fact contains(input_cursor(owner), memory(owner->len));
        fact contains(input_cursor(owner), memory(owner->data));
        fact loadable(owner->pos);
        fact loadable(owner->len);
        fact loadable(owner->data);
        fact 0 <= owner->pos;
        fact owner->pos <= owner->len;
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->len]));
        fact loadable((owner->data)[0..owner->len]);
        fact 0 <= owner->len;
    }
    step using {
        fact owner->pos < owner->len;
        fact separate(memory(owner->pos), memory(owner->len));
        fact separate(memory(owner->pos), memory(owner->data));
        fact separate(memory(owner->len), memory(owner->data));
        fact contains(input_cursor(owner), memory(owner->pos));
        fact contains(input_cursor(owner), memory(owner->len));
        fact contains(input_cursor(owner), memory(owner->data));
        fact loadable(old(owner->pos));
        fact loadable(old(owner->len));
        fact loadable(old(owner->data));
        fact 0 <= owner->pos;
        fact owner->pos <= owner->len;
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->len]));
        fact loadable(old((owner->data)[0..owner->len]));
        fact 0 <= owner->len;
    }
    step using {
        fact owner->pos < owner->len;
        fact separate(memory(owner->pos), memory(owner->len));
        fact separate(memory(owner->pos), memory(owner->data));
        fact separate(memory(owner->len), memory(owner->data));
        fact contains(input_cursor(owner), memory(owner->pos));
        fact contains(input_cursor(owner), memory(owner->len));
        fact contains(input_cursor(owner), memory(owner->data));
        fact loadable(old(owner->pos));
        fact loadable(old(owner->len));
        fact loadable(old(owner->data));
        fact 0 <= owner->pos;
        fact owner->pos <= owner->len;
        fact separate(memory(object(owner)), memory((owner->data)[0..owner->len]));
        fact loadable(old((owner->data)[0..owner->len]));
        fact 0 <= owner->len;
    }
    step();
    have 0 <= owner->pos by {
        derive(0 <= owner->pos) using {
            fact at(statement(2).entry, separate(memory(owner->pos), memory(owner->len)));
            fact at(statement(2).entry, separate(memory(owner->pos), memory(owner->data)));
            fact at(statement(2).entry, separate(memory(owner->len), memory(owner->data)));
            fact at(statement(2).entry, contains(input_cursor(owner), memory(owner->pos)));
            fact at(statement(2).entry, contains(input_cursor(owner), memory(owner->len)));
            fact at(statement(2).entry, contains(input_cursor(owner), memory(owner->data)));
            fact at(statement(2).entry, loadable(old(owner->pos)));
            fact at(statement(2).entry, loadable(old(owner->len)));
            fact at(statement(2).entry, loadable(old(owner->data)));
            fact 0 <= old(owner->pos);
            fact at(statement(2).entry, separate(memory(object(owner)), memory((owner->data)[0..owner->len])));
            fact at(statement(2).entry, loadable(old((owner->data)[0..owner->len])));
            fact old(owner->pos) < owner->len;
            fact old(owner->pos) <= owner->len;
            fact 0 <= owner->len;
        }
    }
    have owner->pos <= owner->len by {
        calculate(owner->pos <= owner->len) using {
            fact old(owner->pos) < owner->len;
        }
    }
    have separate(
        memory(object(owner)),
        memory((owner->data)[0..owner->len])
    ) by {
        simp();
    }
    fold(input_cursor(owner));
    frame();
    have loadable(old((load_int32_pointer(byte_offset(owner, 8)) + load_int32(owner))[0..1])) by {
        derive(loadable(old((load_int32_pointer(byte_offset(owner, 8)) + load_int32(owner))[0..1]))) using {
            fact at(statement(2).entry, separate(memory(owner->pos), memory(owner->len)));
            fact at(statement(2).entry, separate(memory(owner->pos), memory(owner->data)));
            fact at(statement(2).entry, separate(memory(owner->len), memory(owner->data)));
            fact at(statement(2).entry, contains(input_cursor(owner), memory(owner->pos)));
            fact at(statement(2).entry, contains(input_cursor(owner), memory(owner->len)));
            fact at(statement(2).entry, contains(input_cursor(owner), memory(owner->data)));
            fact at(statement(2).entry, loadable(old(owner->pos)));
            fact at(statement(2).entry, loadable(old(owner->len)));
            fact at(statement(2).entry, loadable(old(owner->data)));
            fact 0 <= old(owner->pos);
            fact at(statement(2).entry, separate(memory(object(owner)), memory((owner->data)[0..owner->len])));
            fact at(statement(2).entry, loadable(old((owner->data)[0..owner->len])));
            fact old(owner->pos) < owner->len;
            fact old(owner->pos) <= owner->len;
            fact 0 <= owner->len;
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
        memory((source->data)[0..source->len])
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
    execute_step();
    execute_step();
    step using {
        fact at(statement(0).entry, separate(memory(object(target)), memory(object(source))));
        fact at(statement(0).entry, separate(memory(object(target)), memory((source->data)[0..source->len])));
        fact at(statement(0).entry, loadable(target[0..4]));
        fact at(statement(0).entry, separate(memory(source->pos), memory(source->len)));
        fact at(statement(0).entry, separate(memory(source->pos), memory(source->data)));
        fact at(statement(0).entry, separate(memory(source->len), memory(source->data)));
        fact at(statement(0).entry, contains(input_cursor(source), memory(source->pos)));
        fact at(statement(0).entry, contains(input_cursor(source), memory(source->len)));
        fact at(statement(0).entry, contains(input_cursor(source), memory(source->data)));
        fact at(statement(0).entry, loadable(source->pos));
        fact at(statement(0).entry, loadable(source->len));
        fact at(statement(0).entry, loadable(source->data));
        fact at(statement(0).entry, separate(memory(object(source)), memory((source->data)[0..source->len])));
        fact at(statement(0).entry, loadable((source->data)[0..source->len]));
        fact 0 <= source->pos;
        fact source->pos <= source->len;
        fact 0 <= source->len;
        fact at(statement(1).entry, 0) <= at(statement(1).entry, source->pos);
        fact at(statement(1).entry, source->pos) <= at(statement(1).entry, source->len);
        fact at(statement(1).entry, 0) <= at(statement(1).entry, source->len);
    }
    step using {
        fact separate(memory(object(target)), memory(object(source)));
        fact separate(memory(object(target)), memory((source->data)[0..source->len]));
        fact loadable(old(object(target)));
        fact loadable(old(source->pos));
        fact loadable(old(source->len));
        fact loadable(old(source->data));
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
    have separate(memory(object(right)), memory((left->data)[0..left->len])) by {
        derive(separate(memory(object(right)), memory((left->data)[0..left->len]))) using {
            fact left->len == length;
            fact left->data == data;
            fact separate(memory(object(right)), memory(data[0..length]));
        }
    }
    have left->pos < left->len by {
        derive(left->pos < left->len) using {
            fact 1 <= length;
            fact left->len == length;
            fact left->pos == left_value;
        }
    }
    have left->pos == 0 by {
        simp();
    }
    have left->data == data by {
        simp();
    }
    step using {
        fact left->pos < left->len;
        fact 1 <= length;
        fact left->pos == 0;
        fact left->len == length;
        fact left->data == data;
        fact loadable(old(object(left)));
        fact loadable(old(object(right)));
        fact separate(memory(object(left)), memory(object(right)));
        fact separate(memory(object(left)), memory(data[0..length]));
        fact separate(memory(object(right)), memory((left->data)[0..left->len]));
    }
    transport(at(statement(4).entry, left->pos) < at(statement(4).entry, left->len), left->pos < left->len) using {
        fact at(statement(4).entry, left->pos) < at(statement(4).entry, left->len);
    }
    have right->pos < right->len by {
        derive(right->pos < right->len) using {
            fact left->pos < left->len;
            fact right->len == left->len;
            fact right->pos == left->pos;
        }
    }
    have right->pos == 0 by {
        derive(right->pos == 0) using {
            fact left->pos == left_value;
            fact right->pos == left->pos;
        }
    }
    have right->data == left->data by {
        simp();
    }
    have left->data == data by {
        simp();
    }
    apply(pointer_equality_transitive(right->data, left->data, data));
    step using {
        fact loadable(old(object(left)));
        fact loadable(old(object(right)));
        fact right->data == left->data;
        fact left->data == data;
        fact right->data == data;
        fact 1 <= length;
        fact separate(memory(object(left)), memory(object(right)));
        fact separate(memory(object(left)), memory(data[0..length]));
        fact ignored == left->pos;
        fact right->pos == left->pos;
        fact right->len == left->len;
        fact left->pos < left->len;
        fact left->pos == left_value;
        fact left->len == length;
        fact separate(memory(object(right)), memory(data[0..length]));
        fact separate(memory(left[left_value..4]), memory(right[left_value..4]));
        fact loadable(old(data[0..length]));
        fact 0 <= length;
        fact at(statement(4).entry, left->pos) == at(statement(4).entry, 0);
        fact at(statement(4).entry, left->len) == at(statement(4).entry, length);
        fact at(statement(4).entry, left->data) == at(statement(4).entry, data);
        fact at(statement(4).entry, left->pos) < at(statement(4).entry, left->len);
        fact right->pos < right->len;
        fact right->pos == 0;
    }
    have left->len == left->len by {
        normalize();
    }
    have left->data == left->data by {
        normalize();
    }
    transport(at(statement(5).entry, right->data) == at(statement(5).entry, left->data), right->data == left->data) using {
        fact at(statement(5).entry, right->data) == at(statement(5).entry, left->data);
    }
    transport(at(statement(5).entry, left->data) == data, left->data == data) using {
        fact at(statement(5).entry, left->data) == data;
    }
    transport(at(statement(5).entry, right->data) == data, right->data == data) using {
        fact at(statement(5).entry, right->data) == data;
    }
    transport(at(statement(5).entry, right->pos) == at(statement(5).entry, left->pos), right->pos == at(statement(5).entry, left->pos)) using {
        fact at(statement(5).entry, right->pos) == at(statement(5).entry, left->pos);
    }
    transport(at(statement(5).entry, right->len) == at(statement(5).entry, left->len), right->len == left->len) using {
        fact at(statement(5).entry, right->len) == at(statement(5).entry, left->len);
    }
    transport(at(statement(5).entry, left->pos) < at(statement(5).entry, left->len), at(statement(5).entry, left->pos) < left->len) using {
        fact at(statement(5).entry, left->pos) < at(statement(5).entry, left->len);
    }
    transport(at(statement(5).entry, left->len) == length, left->len == length) using {
        fact at(statement(5).entry, left->len) == length;
    }
    transport(at(statement(5).entry, right->pos) < at(statement(5).entry, right->len), right->pos < right->len) using {
        fact at(statement(5).entry, right->pos) < at(statement(5).entry, right->len);
    }
    transport(at(statement(5).entry, right->pos) == 0, right->pos == 0) using {
        fact at(statement(5).entry, right->pos) == 0;
    }
    have at(statement(5).entry, left->pos) == 0 by {
        simp();
    }
    have left->pos == at(statement(5).entry, left->pos) + 1 by {
        simp();
    }
    apply(incremented_zero_is_one(
        at(statement(5).entry, left->pos),
        left->pos
    ));
    step using {
        fact right->pos < right->len;
        fact 1 <= length;
        fact right->len == left->len;
        fact left->pos == 1;
        fact left->pos == (at(statement(5).entry, left->pos) + 1);
        fact right->pos == right_value;
        fact at(statement(5).entry, left->pos) == 0;
        fact loadable(old(object(left)));
        fact loadable(old(object(right)));
        fact separate(memory(object(left)), memory(data[0..length]));
        fact separate(memory(object(right)), memory(data[0..length]));
        fact right_value <= length;
        fact left->len == left->len;
    }
    have right->pos == 0 by {
        simp();
    }
    have right->data == data by {
        simp();
    }
    have right_value == (right->data)[right->pos] by {
        simp();
    }
    have (right->data)[right->pos] == data[0] by {
        derive((right->data)[right->pos] == data[0]) using {
            fact right->pos == 0;
            fact right->data == data;
        }
    }
    apply(int32_equality_transitive(right_value, (right->data)[right->pos], data[0])) using {
        fact loadable(old(object(right)));
        fact right_value == (right->data)[right->pos];
        fact (right->data)[right->pos] == data[0];
    }
    step using {
        fact at(statement(6).entry, loadable(old(object(right))));
        fact right_value == right->data[right->pos];
        fact right->data[right->pos] == data[0];
        fact right_value == *data;
        fact at(statement(6).entry, 1) <= at(statement(6).entry, length);
        fact at(statement(5).entry, left->pos) == 0;
        fact at(statement(6).entry, loadable(old(object(left))));
        fact at(statement(6).entry, separate(memory(object(left)), memory(data[0..length])));
        fact at(statement(6).entry, separate(memory(object(right)), memory(data[0..length])));
        fact at(statement(6).entry, right_value) <= at(statement(6).entry, length);
        fact right->pos < right->len;
        fact right->len == left->len;
        fact left->pos == 1;
        fact left->pos == at(statement(5).entry, (left->pos + 1));
        fact right->pos == 0;
        fact left->len == left->len;
        fact at(statement(6).entry, left->pos) == at(statement(6).entry, (at(statement(5).entry, left->pos) + 1));
        fact at(statement(5).entry, separate(memory(left[left_value..4]), memory(right[left_value..4])));
        fact at(statement(5).entry, ignored) == at(statement(5).entry, left->pos);
        fact at(statement(4).entry, left->len) == at(statement(4).entry, length);
        fact at(statement(5).entry, loadable(old(data[0..length])));
        fact at(statement(4).entry, left->pos) == at(statement(4).entry, 0);
        fact at(statement(4).entry, left->data) == at(statement(4).entry, data);
        fact at(statement(4).entry, left->pos) < at(statement(4).entry, left->len);
        fact left_value == at(statement(5).entry, left->data[left->pos]);
        fact left->len == at(statement(5).entry, left->len);
        fact left->data == at(statement(5).entry, left->data);
        fact right->data == left->data;
        fact left->data == data;
        fact right->data == data;
        fact right->pos == at(statement(5).entry, left->pos);
        fact at(statement(6).entry, right->len) == at(statement(6).entry, left->len);
        fact at(statement(5).entry, left->pos) < left->len;
        fact at(statement(6).entry, right->pos) < at(statement(6).entry, right->len);
        fact at(statement(6).entry, right->pos) == at(statement(6).entry, right_value);
        fact at(statement(5).entry, right->data) == at(statement(5).entry, left->data);
        fact at(statement(5).entry, left->data) == data;
        fact at(statement(5).entry, right->data) == data;
        fact at(statement(4).entry, separate(memory(object(right)), memory((left->data)[0..left->len])));
        fact at(statement(5).entry, right->pos) == at(statement(5).entry, left->pos);
        fact at(statement(5).entry, right->len) == at(statement(5).entry, left->len);
        fact at(statement(5).entry, left->pos) < at(statement(5).entry, left->len);
        fact at(statement(5).entry, left->len) == length;
        fact at(statement(5).entry, right->pos) < at(statement(5).entry, right->len);
        fact at(statement(5).entry, right->pos) == 0;
        fact at(statement(6).entry, left->len) == at(statement(6).entry, left->len);
        fact left->data == left->data;
        fact left->len == length;
    }
    frame();
    simp();
}
