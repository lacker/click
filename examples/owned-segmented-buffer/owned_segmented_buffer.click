resource owned_segment(data: int32*, length: int32) {
    owns data[0..length];
    fact 0 <= length;
}

resource owned_segmented_buffer(owner: struct owned_segmented_buffer*) {
    owns owner->first_len;
    owns owner->second_len;
    owns owner->first_data;
    owns owner->second_data;
    contains owned_segment(owner->first_data, owner->first_len);
    contains owned_segment(owner->second_data, owner->second_len);
    fact 1 <= owner->first_len;
    fact 1 <= owner->second_len;
}

verifying "owned_segmented_buffer_init.c";
verifying "owned_segmented_buffer_get_first.c";
verifying "owned_segmented_buffer_set_first.c";
verifying "owned_segmented_buffer_set_second.c";
verifying "owned_segmented_buffer_swap.c";
verifying "owned_segmented_buffer_pipeline.c";

int32 owned_segmented_buffer_init(
    struct owned_segmented_buffer* owner,
    int32 first_data[],
    int32 first_len,
    int32 second_data[],
    int32 second_len
) {
    requires 1 <= first_len;
    requires 1 <= second_len;
    consumes owner[0..6];
    consumes first_data[0..first_len];
    consumes second_data[0..second_len];
    mutable owner[0..6];
    produces owned_segmented_buffer(owner);
    ensures result == first_len;
    ensures owner->first_len == first_len;
    ensures owner->second_len == second_len;
    ensures 0 < owner->first_len;
    ensures 0 < owner->second_len;
    ensures owner->first_data == first_data;
    ensures owner->second_data == second_data;
} by {
    execute_rest();
    have 0 <= owner->first_len by { simp(); }
    have 0 <= owner->second_len by { simp(); }
    fold(owned_segment(owner->first_data, owner->first_len));
    fold(owned_segment(owner->second_data, owner->second_len));
    have 1 <= owner->first_len by { simp(); }
    have 1 <= owner->second_len by { simp(); }
    fold(owned_segmented_buffer(owner));
    frame();
    simp();
}

int32 owned_segmented_buffer_get_first(
    struct owned_segmented_buffer* owner,
    int32 index
) {
    requires 0 <= index;
    requires index < owner->first_len;
    views owned_segmented_buffer(owner);
    immutable;
    ensures result == (owner->first_data)[index];
} by {
    observe(owned_segmented_buffer(owner));
    observe(owned_segment(owner->first_data, owner->first_len));
    execute_rest();
    frame();
    simp();
}

int32 owned_segmented_buffer_set_first(
    struct owned_segmented_buffer* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->first_len;
    owns owned_segmented_buffer(owner);
    mutable (owner->first_data)[index..index + 1];
    ensures result == value;
    ensures (owner->first_data)[index] == value;
} by {
    unfold(owned_segmented_buffer(owner));
    unfold(owned_segment(owner->first_data, owner->first_len));
    execute_rest();
    have 0 <= owner->first_len by { simp(); }
    fold(owned_segment(owner->first_data, owner->first_len));
    have 1 <= owner->first_len by { simp(); }
    have 1 <= owner->second_len by { simp(); }
    fold(owned_segmented_buffer(owner));
    have index < index + 1 by { simp(); }
    frame();
    simp();
}

int32 owned_segmented_buffer_set_second(
    struct owned_segmented_buffer* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->second_len;
    owns owned_segmented_buffer(owner);
    mutable (owner->second_data)[index..index + 1];
    ensures result == value;
    ensures (owner->second_data)[index] == value;
} by {
    unfold(owned_segmented_buffer(owner));
    unfold(owned_segment(owner->second_data, owner->second_len));
    execute_rest();
    have 0 <= owner->second_len by { simp(); }
    fold(owned_segment(owner->second_data, owner->second_len));
    have 1 <= owner->first_len by { simp(); }
    have 1 <= owner->second_len by { simp(); }
    fold(owned_segmented_buffer(owner));
    have index < index + 1 by { simp(); }
    frame();
    simp();
}

int32 owned_segmented_buffer_swap(struct owned_segmented_buffer* owner) {
    owns owned_segmented_buffer(owner);
    mutable owner[0..6];
    ensures result == old(owner->second_len);
    ensures owner->first_len == old(owner->second_len);
    ensures owner->second_len == old(owner->first_len);
    ensures 0 < owner->first_len;
    ensures 0 < owner->second_len;
    ensures owner->first_data == old(owner->second_data);
    ensures owner->second_data == old(owner->first_data);
} by {
    unfold(owned_segmented_buffer(owner));
    execute_rest();
    have 1 <= owner->first_len by { simp(); }
    have 1 <= owner->second_len by { simp(); }
    fold(owned_segmented_buffer(owner));
    frame();
    simp();
}

int32 owned_segmented_buffer_pipeline(
    struct owned_segmented_buffer* owner,
    int32 first_data[],
    int32 first_len,
    int32 second_data[],
    int32 second_len,
    int32 first_value,
    int32 second_value
) {
    requires 1 <= first_len;
    requires 1 <= second_len;
    consumes owner[0..6];
    consumes first_data[0..first_len];
    consumes second_data[0..second_len];
    produces owned_segmented_buffer(owner);
    ensures owner->first_len == first_len;
    ensures owner->second_len == second_len;
    ensures owner->first_data == first_data;
    ensures owner->second_data == second_data;
    ensures first_data[0] == first_value;
    ensures second_data[0] == second_value;
    ensures result == first_value;
} by {
    execute_rest();
    simp();
}
