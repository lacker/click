theorem incremented_zero_is_one(before: int32, after: int32) {
    requires before == 0;
    requires after == before + 1;

    ensures after == 1 by {
        rewrite(after == before + 1);
        rewrite(before == 0);
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
    step();
    step();
    step();
    step();
    have 0 <= owner->pos by {
        simp() using {
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
        simp() using {
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
        simp() using {
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
    step();
    step();
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
        simp() using {
            left->len == length;
            left->data == data;
            separate(memory(object(right)), memory(data[0..length]));
        }
    }
    have left->pos == 0 by simp;
    have left->pos < left->len by {
        simp() using {
            1 <= length;
            left->len == length;
            left->pos == 0;
        }
    }
    have left->data == data by simp;
    step();
    transport(at(statement(4).entry, left->pos) < at(statement(4).entry, left->len), left->pos < left->len) using {
        at(statement(4).entry, left->pos) < at(statement(4).entry, left->len);
    }
    have right->pos < right->len by {
        simp() using {
            1 <= length;
            right->len == length;
            right->pos == 0;
        }
    }
    have right->pos == 0 by simp;
    have right->data == data by simp;
    have left->data == data by {
        transport(at(statement(4).entry, left->data) == data, left->data == data) using {
            at(statement(4).entry, left->data) == data;
        }
        assumption();
    }
    step();
    have left->len == left->len by {
        normalize();
    }
    have left->data == left->data by {
        normalize();
    }
    transport(at(statement(5).entry, right->len) == length, right->len == length) using {
        at(statement(5).entry, right->len) == length;
    }
    transport(at(statement(4).entry, left->len) == length, left->len == length) using {
        at(statement(4).entry, left->len) == length;
    }
    have right->pos == 0 by {
        transport(at(statement(5).entry, right->pos) == 0, right->pos == 0) using {
            at(statement(5).entry, right->pos) == 0;
        }
        assumption();
    }
    have 0 < right->len by {
        simp() using {
            right->len == length;
            1 <= length;
        }
    }
    have right->pos < right->len by {
        simp() using {
            right->pos == 0;
            0 < right->len;
        }
    }
    have right->data == data by {
        transport(at(statement(5).entry, right->data) == data, right->data == data) using {
            at(statement(5).entry, right->data) == data;
        }
        assumption();
    }
    have at(statement(5).entry, left->pos) == 0 by simp;
    have left->pos == at(statement(5).entry, left->pos) + 1 by simp;
    apply(incremented_zero_is_one(
        at(statement(5).entry, left->pos),
        left->pos
    ));
    step();
    have right_value == right->data[right->pos] by {
        assumption();
    }
    have right->pos == 0 by simp;
    have right->data == data by simp;
    have right_value == right->data[right->pos] by simp;
    have right->data[right->pos] == data[0] by {
        simp() using {
            right->pos == 0;
            right->data == data;
        }
    }
    apply(int32_equality_transitive(right_value, right->data[right->pos], data[0])) using {
        loadable(old(object(right)));
        right_value == right->data[right->pos];
        right->data[right->pos] == data[0];
    }
    step();
    frame();
    simp();
}
