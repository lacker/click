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
    execute_rest();
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
    execute_rest();
    frame();
    simp();
}
