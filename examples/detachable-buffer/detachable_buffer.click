resource detached_buffer(owner: struct detachable_buffer*) {
    owns owner->len;
    owns owner->data;
    fact 1 <= owner->len;
    fact separate(
        memory(object(owner)),
        memory(owner->data[0..owner->len])
    );
}

resource detached_backing(data: int32*, length: int32) {
    owns data[0..length];
    fact 1 <= length;
}

resource attached_buffer(owner: struct detachable_buffer*) {
    owns owner->len;
    owns owner->data;
    owns owner->data[0..owner->len];
    fact 1 <= owner->len;
    fact separate(
        memory(object(owner)),
        memory(owner->data[0..owner->len])
    );
}

verifying "buffer_init.c";
verifying "buffer_detach.c";
verifying "buffer_set_first.c";
verifying "buffer_attach.c";
verifying "buffer_get.c";
verifying "buffer_pipeline.c";

int32 detachable_buffer_init(
    struct detachable_buffer* owner,
    int32 data[],
    int32 length
) {
    requires 1 <= length;
    consumes object(owner);
    consumes data[0..length];
    mutable owner->len, owner->data;
    produces attached_buffer(owner);

    ensures result == length;
    ensures owner->len == length;
    ensures owner->data == data;
} by {
    execute();
    fold(attached_buffer(owner));
    frame();
    simp();
}

int32 detachable_buffer_detach(
    struct detachable_buffer* owner,
    int32 data[],
    int32 length
) {
    requires owner->data == data;
    requires owner->len == length;
    consumes attached_buffer(owner);
    mutable owner->len, owner->data;
    produces detached_buffer(owner);
    produces detached_backing(data, length);

    ensures result == 0;
    ensures owner->len == length;
    ensures owner->data == data;
} by {
    unfold(attached_buffer(owner));
    execute();
    fold(detached_backing(data, length));
    fold(detached_buffer(owner));
    frame();
    simp();
}

int32 detachable_buffer_set_first(
    int32 data[],
    int32 length,
    int32 value
) {
    requires 1 <= length;
    owns detached_backing(data, length);
    mutable data[0..1];

    ensures result == value;
    ensures data[0] == value;
} by {
    unfold(detached_backing(data, length));
    execute();
    fold(detached_backing(data, length));
    frame();
    simp();
}

int32 detachable_buffer_attach(
    struct detachable_buffer* owner,
    int32 data[],
    int32 length
) {
    requires 1 <= length;
    consumes detached_buffer(owner);
    consumes detached_backing(data, length);
    mutable owner->len, owner->data;
    produces attached_buffer(owner);

    ensures result == length;
    ensures owner->len == length;
    ensures owner->data == data;
} by {
    unfold(detached_buffer(owner));
    unfold(detached_backing(data, length));
    execute();
    fold(attached_buffer(owner));
    frame();
    simp();
}

int32 detachable_buffer_get(
    struct detachable_buffer* owner,
    int32 index
) {
    requires 0 <= index;
    requires index < owner->len;
    views attached_buffer(owner);
    immutable;

    ensures result == owner->data[index] by auto;
}

int32 detachable_buffer_pipeline(
    struct detachable_buffer* owner,
    int32 data[],
    int32 length,
    int32 replacement
) {
    requires 1 <= length;
    consumes object(owner);
    consumes data[0..length];
    mutable object(owner), data[0..1];
    produces attached_buffer(owner);

    ensures result == replacement;
    ensures owner->len == length;
    ensures owner->data == data;
    ensures data[0] == replacement;
} by {
    execute();
    frame();
    have result == replacement by {
        assumption();
    }
    have owner->len == length by {
        assumption();
    }
    have owner->data == data by {
        assumption();
    }
    have data[0] == replacement by {
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}
