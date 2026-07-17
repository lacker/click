resource owned_split_buffer(owner: struct owned_split_buffer*) {
    owns owner->split;
    owns owner->len;
    owns owner->data;
    owns (owner->data)[0..owner->split];
    owns (owner->data)[owner->split..owner->len];
    fact 0 <= owner->split;
    fact owner->split <= owner->len;
    fact separate(
        memory(owner[0..4]),
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
    consumes owner[0..4];
    consumes data[0..length];
    mutable owner[0..4];
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
} by {
    unfold(owned_split_buffer(owner));
    execute_rest();
    fold(owned_split_buffer(owner));
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
} by {
    unfold(owned_split_buffer(owner));
    execute_rest();
    fold(owned_split_buffer(owner));
    frame();
    simp();
}

int32 owned_split_buffer_move_right(struct owned_split_buffer* owner) {
    requires owner->split < owner->len;
    owns owned_split_buffer(owner);
    mutable_field(owner->split);
    ensures result == old(owner->split) + 1;
    ensures owner->split == old(owner->split) + 1;
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    unfold(owned_split_buffer(owner));
    execute_rest();
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
    consumes owner[0..4];
    consumes data[0..length];
    produces owned_split_buffer(owner);
    ensures owner->split == 2;
    ensures owner->len == length;
    ensures owner->data == data;
    ensures data[0] == left_value;
    ensures data[1] == right_value;
    ensures result == right_value;
} by {
    execute_until(statement(4));
    have 1 < owner->len by {
        simp();
    }
    execute_until(statement(5));
    have owner->split < owner->len by {
        simp();
    }
    execute_until(statement(6));
    have 1 < owner->split by {
        simp();
    }
    execute_rest();
    simp();
}
