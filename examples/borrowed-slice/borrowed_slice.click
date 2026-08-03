resource owned_borrowable_buffer(
    owner: struct borrowed_slice_buffer*,
    data: int32*,
    length: int32
) {
    owns owner->len;
    owns owner->data;
    owns data[0..length];
    fact owner->len == length;
    fact owner->data == data;
    fact 1 <= length;
    fact separate(
        memory(object(owner)),
        memory(data[0..length])
    );
}

resource buffer_without_slice(
    owner: struct borrowed_slice_buffer*,
    data: int32*,
    length: int32,
    start: int32,
    end: int32
) {
    owns owner->len;
    owns owner->data;
    owns data[0..start];
    owns data[end..length];
    fact owner->len == length;
    fact owner->data == data;
    fact 0 <= start;
    fact start < end;
    fact end <= length;
    fact 1 <= length;
    fact separate(memory(object(owner)), memory(data[0..length]));
}

resource owned_slice(
    data: int32*,
    start: int32,
    end: int32
) {
    owns data[start..end];
    fact 0 <= start;
    fact start < end;
}

verifying "buffer_init.c";
verifying "buffer_borrow.c";
verifying "slice_set.c";
verifying "buffer_return.c";
verifying "buffer_get.c";
verifying "buffer_pipeline.c";

int32 borrowed_slice_buffer_init(
    struct borrowed_slice_buffer* owner,
    int32 data[],
    int32 length
) {
    requires 1 <= length;
    consumes object(owner);
    consumes data[0..length];
    mutable owner->len, owner->data;
    produces owned_borrowable_buffer(owner, data, length);

    ensures result == length;
    ensures owner->len == length;
    ensures owner->data == data;
} by {
    execute();
    fold(owned_borrowable_buffer(owner, data, length));
    frame();
    simp();
}

int32 borrowed_slice_buffer_borrow(
    struct borrowed_slice_buffer* owner,
    int32 data[],
    int32 length,
    int32 start,
    int32 end
) {
    requires owner->len == length;
    requires owner->data == data;
    requires 0 <= start;
    requires start < end;
    requires end <= length;
    requires 1 <= length;
    consumes owned_borrowable_buffer(owner, data, length);
    mutable owner->len, owner->data;
    produces buffer_without_slice(owner, data, length, start, end);
    produces owned_slice(data, start, end);

    ensures result == start;
    ensures owner->len == length;
    ensures owner->data == data;
} by {
    unfold(owned_borrowable_buffer(owner, data, length));
    execute();
    fold(owned_slice(data, start, end));
    fold(buffer_without_slice(owner, data, length, start, end));
    frame();
    simp();
}

int32 borrowed_slice_set(
    int32 data[],
    int32 start,
    int32 end,
    int32 index,
    int32 value
) {
    requires start <= index;
    requires index < end;
    owns owned_slice(data, start, end);
    mutable data[index..index + 1];

    ensures result == value;
    ensures data[index] == value;
} by {
    unfold(owned_slice(data, start, end));
    execute();
    fold(owned_slice(data, start, end));
    frame();
    simp();
}

int32 borrowed_slice_buffer_return(
    struct borrowed_slice_buffer* owner,
    int32 data[],
    int32 length,
    int32 start,
    int32 end
) {
    consumes buffer_without_slice(owner, data, length, start, end);
    consumes owned_slice(data, start, end);
    mutable owner->len, owner->data;
    produces owned_borrowable_buffer(owner, data, length);

    ensures result == length;
    ensures owner->len == length;
    ensures owner->data == data;
} by {
    unfold(buffer_without_slice(owner, data, length, start, end));
    unfold(owned_slice(data, start, end));
    execute();
    fold(owned_borrowable_buffer(owner, data, length));
    frame();
    simp();
}

int32 borrowed_slice_buffer_get(
    struct borrowed_slice_buffer* owner,
    int32 data[],
    int32 length,
    int32 index
) {
    requires 0 <= index;
    requires index < length;
    views owned_borrowable_buffer(owner, data, length);
    immutable;

    ensures result == data[index] by auto;
}

int32 borrowed_slice_buffer_pipeline(
    struct borrowed_slice_buffer* owner,
    int32 data[],
    int32 length,
    int32 start,
    int32 end,
    int32 replacement
) {
    requires 0 <= start;
    requires start < end;
    requires end <= length;
    requires 1 <= length;
    consumes object(owner);
    consumes data[0..length];
    mutable object(owner), data[start..start + 1];
    produces owned_borrowable_buffer(owner, data, length);

    ensures result == replacement;
    ensures owner->len == length;
    ensures owner->data == data;
    ensures data[start] == replacement;
} by {
    execute();
    frame();
    simp();
}
