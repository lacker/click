resource ring_frame(owner: struct ring_buffer*) {
    owns owner->head;
    owns owner->data;
    owns owner->data[0..4];
    fact 2 <= owner->head;
    fact owner->head < 4;
    fact separate(memory(object(owner)), memory(owner->data[0..4]));
}

resource linear_ring(owner: struct ring_buffer*) {
    owns owner->tail;
    contains ring_frame(owner);
    fact owner->tail == 4;
}

resource wrapped_ring(owner: struct ring_buffer*) {
    owns owner->tail;
    contains ring_frame(owner);
    fact owner->tail == 1;
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
    produces linear_ring(owner);

    ensures result == 4;
    ensures owner->head == head;
    ensures owner->tail == 4;
    ensures owner->data == data;
} by {
    execute();
    fold(ring_frame(owner));
    fold(linear_ring(owner));
    simp();
}

int32 ring_buffer_push_wrap(
    struct ring_buffer* owner,
    int32 value
) {
    requires owner->tail == 4;
    requires 2 <= owner->head;
    requires owner->head < 4;
    requires separate(memory(object(owner)), memory(owner->data[0..4]));
    views owner->head;
    views owner->data;
    views owner->data[1..4];
    owns owner->tail;
    owns owner->data[0..1];

    ensures result == value;
    ensures owner->data[0] == value;
    ensures owner->head == old(owner->head);
    ensures owner->tail == 1;
    ensures owner->data == old(owner->data);
} by {
    execute();
    simp();
}

int32 ring_buffer_wrapped_tail(
    struct ring_buffer* owner
) {
    views wrapped_ring(owner);

    ensures result == owner->data[0];
} by {
    observe(wrapped_ring(owner));
    observe(ring_frame(owner));
    execute();
    simp();
}

int32 ring_buffer_pop_to_linear(
    struct ring_buffer* owner
) {
    requires owner->tail == 1;
    requires 2 <= owner->head;
    requires owner->head < 4;
    requires separate(memory(object(owner)), memory(owner->data[0..4]));
    views owner->head;
    views owner->data;
    views owner->data[0..4];
    owns owner->tail;

    ensures result == old(owner->data[0]);
    ensures owner->head == old(owner->head);
    ensures owner->tail == 4;
    ensures owner->data == old(owner->data);
} by {
    execute();
    simp();
}

int32 ring_buffer_pipeline(
    struct ring_buffer* owner,
    int32 replacement
) {
    consumes linear_ring(owner);
    produces linear_ring(owner);

    ensures result == replacement;
    ensures owner->head == old(owner->head);
    ensures owner->tail == 4;
    ensures owner->data == old(owner->data);
    ensures owner->data[0] == replacement;
} by {
    unfold(linear_ring(owner));
    unfold(ring_frame(owner));
    execute();
    fold(ring_frame(owner));
    fold(linear_ring(owner));
    have result == replacement by {
        rewrite(at(statement(4).entry, pushed) ==
            at(statement(4).entry, replacement));
        normalize();
    }
    have owner->head == old(owner->head) by {
        normalize();
    }
    have owner->tail == 4 by {
        assumption();
    }
    have owner->data == old(owner->data) by {
        normalize();
    }
    have owner->data[0] == replacement by {
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}
