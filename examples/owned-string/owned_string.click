predicate terminated_at(int32 data[], int32 length) {
    data[length] == 0
}

resource owned_string(owner: struct owned_string*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(owner[0..4]),
        memory((owner->data)[0..owner->cap])
    );
}

verifying "owned_string_init.c";
verifying "owned_string_len.c";
verifying "owned_string_get.c";
verifying "owned_string_set.c";
verifying "owned_string_push.c";
verifying "owned_string_push_preserves_first.c";
verifying "owned_string_pop.c";
verifying "owned_string_pop_preserves_first.c";
verifying "owned_string_clear.c";
verifying "owned_string_pipeline.c";

int32 owned_string_init(
    struct owned_string* owner,
    int32 data[],
    int32 capacity
) {
    requires 1 <= capacity;
    consumes owner[0..4];
    consumes data[0..capacity];
    mutable owner[0..4], data[0..1];
    produces owned_string(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->cap == capacity;
    ensures owner->data == data;
    ensures data[0] == 0;
} by {
    execute_rest();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        simp();
    }
    fold(owned_string(owner));
    frame();
    simp();
}

int32 owned_string_len(struct owned_string* owner) {
    views owned_string(owner);
    immutable;

    ensures result == owner->len by auto;
}

int32 owned_string_get(struct owned_string* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views owned_string(owner);
    immutable;

    ensures result == (owner->data)[index] by auto;
}

int32 owned_string_set(
    struct owned_string* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->len;
    owns owned_string(owner);
    mutable (owner->data)[index..index + 1];

    ensures result == value;
    ensures (owner->data)[index] == value;
} by {
    unfold(owned_string(owner));
    execute_step();
    fold(owned_string(owner));
    execute_step();
    frame();
    simp();
}

int32 owned_string_push(struct owned_string* owner, int32 value) {
    requires owner->len + 1 < owner->cap;
    owns owned_string(owner);
    mutable owner[0..1], (owner->data + owner->len)[0..2];
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures (owner->data)[old(owner->len)] == value;
    ensures (owner->data)[owner->len] == 0;
} by {
    unfold(owned_string(owner));
    execute_rest();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        simp();
    }
    fold(owned_string(owner));
    frame();
    simp();
}

int32 owned_string_push_preserves_first(
    struct owned_string* owner,
    int32 value
) {
    let data = old(owner->data);

    requires 1 <= owner->len;
    requires owner->len + 1 < owner->cap;
    owns owned_string(owner);
    mutable owner[0..1], (owner->data + owner->len)[0..2];

    ensures result == old(owner->len) + 1;
    ensures data[0] == old(data[0]);
} by {
    execute_rest();
    frame();
    simp();
}

int32 owned_string_pop(struct owned_string* owner) {
    requires 1 <= owner->len;
    owns owned_string(owner);
    mutable owner[0..1], (owner->data + (owner->len - 1))[0..1];
    ensures result == old((owner->data)[owner->len - 1]);
    ensures owner->len == old(owner->len) - 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures (owner->data)[owner->len] == 0;
} by {
    unfold(owned_string(owner));
    have 0 <= owner->len - 1 by {
        simp();
    }
    have owner->len - 1 < owner->len by {
        simp();
    }
    execute_rest();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        simp();
    }
    fold(owned_string(owner));
    frame();
    simp();
}

int32 owned_string_pop_preserves_first(struct owned_string* owner) {
    let data = old(owner->data);

    requires 2 <= owner->len;
    owns owned_string(owner);
    mutable owner[0..1], (owner->data + (owner->len - 1))[0..1];

    ensures result == old((owner->data)[owner->len - 1]);
    ensures data[0] == old(data[0]);
} by {
    execute_rest();
    frame();
    simp();
}

int32 owned_string_clear(struct owned_string* owner) {
    owns owned_string(owner);
    mutable owner[0..1], (owner->data)[0..1];
    ensures result == 0;
    ensures owner->len == 0;
    ensures (owner->data)[0] == 0;
} by {
    unfold(owned_string(owner));
    execute_rest();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at);
        simp();
    }
    fold(owned_string(owner));
    frame();
    simp();
}

int32 owned_string_pipeline(
    struct owned_string* owner,
    int32 data[],
    int32 capacity,
    int32 first
) {
    requires 2 <= capacity;
    consumes owner[0..4];
    consumes data[0..capacity];
    produces owned_string(owner);
    ensures owner->len == 0;
    ensures result == first;
} by {
    execute_rest();
    simp();
}
