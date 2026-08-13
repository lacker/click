resource owned_ring_storage(data: int32*) {
    owns data[0..4];
}

resource linear_ring(owner: struct ring_buffer*) {
    owns owner->head;
    owns owner->tail;
    owns owner->data;
    contains owned_ring_storage(owner->data);
    fact 2 <= owner->head;
    fact owner->head < 4;
    fact owner->tail == 4;
    fact separate(memory(object(owner)), memory(owner->data[0..4]));
}

resource wrapped_ring(owner: struct ring_buffer*) {
    owns owner->head;
    owns owner->tail;
    owns owner->data;
    contains owned_ring_storage(owner->data);
    fact 2 <= owner->head;
    fact owner->head < 4;
    fact owner->tail == 1;
    fact separate(memory(object(owner)), memory(owner->data[0..4]));
}

verifying "ring_init_linear.c";
verifying "ring_push_wrap.c";
verifying "ring_wrapped_tail.c";
verifying "ring_pop_to_linear.c";
verifying "ring_pipeline.c";

int32 ring_buffer_init_linear(
    struct ring_buffer* owner,
    int32 data[],
    int32 head
) {
    requires 2 <= head;
    requires head < 4;
    consumes object(owner);
    consumes data[0..4];
    mutable owner->head, owner->tail, owner->data;
    produces linear_ring(owner);

    ensures result == 4;
    ensures owner->head == head;
    ensures owner->tail == 4;
    ensures owner->data == data;
} by {
    execute();
    fold(owned_ring_storage(owner->data));
    fold(linear_ring(owner));
    frame();
    simp();
}

int32 ring_buffer_push_wrap(
    struct ring_buffer* owner,
    int32 value
) {
    consumes linear_ring(owner);
    mutable owner->tail, owner->data[0..1];
    produces wrapped_ring(owner);

    ensures result == value;
    ensures owner->data[0] == value;
    ensures owner->head == old(owner->head);
    ensures owner->tail == 1;
    ensures owner->data == old(owner->data);
} by {
    unfold(linear_ring(owner));
    unfold(owned_ring_storage(owner->data));
    execute();
    fold(owned_ring_storage(owner->data));
    fold(wrapped_ring(owner));
    frame();
    simp();
}

int32 ring_buffer_wrapped_tail(
    struct ring_buffer* owner
) {
    views wrapped_ring(owner);
    immutable;

    ensures result == owner->data[0];
} by {
    observe(wrapped_ring(owner));
    observe(owned_ring_storage(owner->data));
    execute();
    frame();
    simp();
}

int32 ring_buffer_pop_to_linear(
    struct ring_buffer* owner
) {
    consumes wrapped_ring(owner);
    mutable owner->tail;
    produces linear_ring(owner);

    ensures result == old(owner->data[0]);
    ensures owner->head == old(owner->head);
    ensures owner->tail == 4;
    ensures owner->data == old(owner->data);
} by {
    unfold(wrapped_ring(owner));
    unfold(owned_ring_storage(owner->data));
    execute();
    fold(owned_ring_storage(owner->data));
    fold(linear_ring(owner));
    frame();
    simp();
}

int32 ring_buffer_pipeline(
    struct ring_buffer* owner,
    int32 replacement
) {
    consumes linear_ring(owner);
    mutable owner->tail, owner->data[0..1];
    produces linear_ring(owner);

    ensures result == replacement;
    ensures owner->head == old(owner->head);
    ensures owner->tail == 4;
    ensures owner->data == old(owner->data);
    ensures owner->data[0] == replacement;
} by {
    execute();
    frame() using {
        at(statement(4).entry, separate(memory(owner->head), memory(owner->tail)));
        at(statement(4).entry, separate(memory(owner->head), memory(owner->data)));
        at(statement(4).entry, separate(memory(owner->tail), memory(owner->data)));
        at(statement(4).entry, separate(memory(owner->head), owned_ring_storage(owner->data)));
        at(statement(4).entry, separate(memory(owner->tail), owned_ring_storage(owner->data)));
        at(statement(4).entry, separate(memory(owner->data), owned_ring_storage(owner->data)));
        at(statement(4).entry, loadable(old(owner->head)));
        at(statement(4).entry, loadable(old(owner->tail)));
        at(statement(4).entry, loadable(old(owner->data)));
        at(statement(4).entry, 2) <= at(statement(4).entry, owner->head);
        at(statement(4).entry, owner->head) < at(statement(4).entry, 4);
        at(statement(2).entry, owner->tail) == at(statement(2).entry, 4);
        at(statement(4).entry, separate(memory(object(owner)), memory(owner->data[0..4])));
        at(statement(4).entry, pushed) == at(statement(4).entry, replacement);
        at(statement(4).entry, owner->data[0]) == at(statement(4).entry, replacement);
        at(statement(3).entry, owner->tail) == at(statement(3).entry, 1);
        at(statement(4).entry, ignored) == at(statement(4).entry, owner->data[0]);
        at(statement(4).entry, owner->head) == at(statement(4).entry, owner->head);
        contains(linear_ring(owner), memory(owner->head));
        contains(linear_ring(owner), memory(owner->tail));
        contains(linear_ring(owner), memory(owner->data));
        contains(linear_ring(owner), owned_ring_storage(owner->data));
    }
    simp();
}
