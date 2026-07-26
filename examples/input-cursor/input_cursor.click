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
        memory(owner[0..4]),
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
    requires separate(memory(owner[0..4]), memory(data[0..length]));
    consumes owner[0..4];
    views readable_input(data, length);
    mutable owner[0..4];
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
    execute_rest();
    have 0 <= owner->pos by { simp(); }
    have owner->pos <= owner->len by { simp(); }
    have separate(
        memory(owner[0..4]),
        memory((owner->data)[0..owner->len])
    ) by {
        simp();
    }
    fold(input_cursor(owner));
    frame();
    simp();
}

int32 input_cursor_clone(
    struct input_cursor* target,
    struct input_cursor* source
) {
    requires separate(memory(target[0..4]), memory(source[0..4]));
    requires separate(
        memory(target[0..4]),
        memory((source->data)[0..source->len])
    );
    consumes target[0..4];
    views input_cursor(source);
    mutable target[0..4];
    produces input_cursor(target);
    ensures result == source->pos;
    ensures target->pos == source->pos;
    ensures target->len == source->len;
    ensures target->data == source->data;
} by {
    observe(input_cursor(source));
    execute_step();
    execute_step();
    execute_step();
    step using {
        fact separate(memory(target[0..4]), memory(source[0..4]));
        fact separate(memory(target[0..4]), memory(load_int32_pointer((source + 2))[0..load_int32((source + 1))]));
        fact loadable(old(target[0..4]));
        fact loadable(old(source[0..1]));
        fact loadable(old((source + 1)[0..1]));
        fact loadable(old((source + 2)[0..2]));
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
    requires separate(memory(left[0..4]), memory(data[0..length]));
    requires separate(memory(right[0..4]), memory(data[0..length]));
    consumes left[0..4];
    consumes right[0..4];
    views readable_input(data, length);
    mutable left[0..4], right[0..4];
    produces input_cursor(left);
    produces input_cursor(right);
    ensures left->pos == 1;
    ensures right->pos == 0;
    ensures result == data[0];
} by {
    execute_until(statement(4));
    have separate(memory(right[0..4]), memory(load_int32_pointer((left + 2))[0..load_int32((left + 1))])) by {
        derive(separate(memory(right[0..4]), memory(load_int32_pointer((left + 2))[0..load_int32((left + 1))]))) using {
            fact *(left + 1) == length;
            fact load_int32_pointer((left + 2)) == data;
            fact separate(memory(right[0..4]), memory(data[0..length]));
        }
    }
    have left->pos < left->len by {
        derive(load_int32(left) < load_int32((left + 1))) using {
            fact 1 <= length;
            fact *(left + 1) == length;
            fact *left == left_value;
        }
    }
    have left->pos == 0 by {
        simp();
    }
    have left->data == data by {
        simp();
    }
    step using {
        fact *left < *(left + 1);
        fact 1 <= length;
        fact *left == 0;
        fact *(left + 1) == length;
        fact load_int32_pointer((left + 2)) == data;
        fact loadable(old(left[0..4]));
        fact loadable(old(right[0..4]));
        fact separate(memory(right[0..4]), memory(left[0..4]));
        fact separate(memory(left[0..4]), memory(data[0..length]));
        fact separate(memory(right[0..4]), memory(load_int32_pointer((left + 2))[0..load_int32((left + 1))]));
    }
    have load_int32(right) < load_int32((right + 1)) by {
        calculate(load_int32(right) < load_int32((right + 1))) using {
            fact 1 <= length;
            fact *(left + 1) == length;
            fact *(right + 1) == *(left + 1);
            fact *left == left_value;
            fact *right == *left;
        }
    }
    have load_int32(right) == 0 by {
        derive(load_int32(right) == 0) using {
            fact *left == left_value;
            fact *right == *left;
        }
    }
    have right->data == left->data by {
        simp();
    }
    have left->data == data by {
        simp();
    }
    apply(pointer_equality_transitive(right->data, left->data, data));
    execute_step();
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
        fact *right < *(right + 1);
        fact 1 <= length;
        fact *(right + 1) == *(left + 1);
        fact *left == 1;
        fact load_int32(left) == (at(statement(5).entry, load_int32(left)) + 1);
        fact *right == right_value;
        fact at(statement(5).entry, load_int32(left)) == 0;
        fact loadable(old(left[0..4]));
        fact loadable(old(right[0..4]));
        fact separate(memory(left[0..4]), memory(data[0..length]));
        fact separate(memory(right[0..4]), memory(data[0..length]));
        fact right_value <= length;
        fact *(left + 1) == *(left + 1);
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
        simp();
    }
    apply(int32_equality_transitive(
        right_value,
        (right->data)[right->pos],
        data[0]
    ));
    execute_rest();
    frame();
    simp();
}
