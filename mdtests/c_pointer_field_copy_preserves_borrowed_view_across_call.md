# A C pointer-field copy preserves the input view across a modular call

The initializer, resource and contract retain the original cursor pattern.
The caller must receive a view of the same input, alongside descriptor ownership.

```c filename=probe.c
struct input_cursor {
    int32 pos;
    int32 len;
    int32* data;
};

int32 input_cursor_init(
    struct input_cursor* owner,
    int32 data[],
    int32 length
) {
    owner->pos = 0;
    owner->len = length;
    owner->data = data;
    return 0;
}

int32 caller(struct input_cursor* owner, int32 data[], int32 length) {
    return input_cursor_init(owner, data, length);
}
```

```click
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
        memory(*owner),
        memory(owner->data[0..owner->len])
    );
}

verifying "probe.c";

int32 input_cursor_init(
    struct input_cursor* owner,
    int32 data[],
    int32 length
) {
    requires 0 <= length;
    requires separate(memory(*owner), memory(data[0..length]));
    consumes *owner;
    views readable_input(data, length);

    produces input_cursor(owner);
    ensures result == 0;
    ensures owner->pos == 0;
    ensures owner->len == length;
    ensures owner->data == data;
} by {
    execute();
    fold(input_cursor(owner));
    simp();
}


int32 caller(struct input_cursor* owner, int32 data[], int32 length) {
    requires 0 <= length;
    requires separate(memory(*owner), memory(data[0..length]));
    consumes *owner;
    views readable_input(data, length);
    produces input_cursor(owner);
    ensures result == 0;
    ensures owner->data == data;
    ensures owner->len == length;
} by { execute(); simp(); }
```

```expect
pass
```
