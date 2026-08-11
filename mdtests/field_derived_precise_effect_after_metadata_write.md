# Field-derived precise effects survive metadata writes

This checks that a mutable footprint evaluated at function entry remains usable
after the function updates neighboring metadata. `buffer_push` writes only the
old end cell, its successor, and `owner->len`. The modular caller therefore
proves that the earlier `data[0]` cell is unchanged when the old length is
positive.

```c filename=field_derived_buffer_push.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_push(struct buffer* owner, int32 value) {
    int32 index;
    index = owner->len;
    owner->data[index] = value;
    owner->len = index + 1;
    owner->data[index + 1] = 0;
    return index + 1;
}
```

```c filename=field_derived_buffer_push_preserves_first.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_push_preserves_first(
    struct buffer* owner,
    int32 data[],
    int32 value
) {
    int32 ignored;
    ignored = buffer_push(owner, value);
    return ignored;
}
```

```click
verifying "field_derived_buffer_push.c";
verifying "field_derived_buffer_push_preserves_first.c";

resource owned_buffer(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact separate(
        memory(owner[0..4]),
        memory(owner->data[0..owner->cap])
    );
}

int32 buffer_push(struct buffer* owner, int32 value) {
    requires owner->len + 1 < owner->cap;
    owns owned_buffer(owner);
    mutable owner[0..1],
        (owner->data + owner->len)[0..2];

    ensures result == old(owner->len) + 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    unfold(owned_buffer(owner));
    execute();
    have 0 <= owner->len by simp;
    have owner->len < owner->cap by {
        transport(
            at(statement(4).entry, (index + 1)) <
                at(statement(4).entry, owner->cap),
            owner->len < owner->cap
        ) using {
            at(statement(4).entry, (index + 1)) < at(statement(4).entry, owner->cap);
            at(statement(5).entry, separate(memory(owner->len), memory(owner->cap)));
            at(statement(5).entry, separate(memory(owner->len), memory(owner->data)));
            at(statement(5).entry, separate(memory(owner->cap), memory(owner->data)));
            at(statement(5).entry, loadable(old(owner->len)));
            at(statement(5).entry, loadable(old(owner->cap)));
            at(statement(5).entry, loadable(old(owner->data)));
            at(statement(5).entry, loadable(old(owner->data[0..owner->cap])));
            at(statement(5).entry, 0) <= at(statement(5).entry, index);
            at(statement(4).entry, index) < at(statement(4).entry, owner->cap);
            at(statement(4).entry, separate(memory(owner[0..4]), memory(owner->data[0..owner->cap])));
            contains(owned_buffer(owner), memory(owner->len));
            contains(owned_buffer(owner), memory(owner->cap));
            contains(owned_buffer(owner), memory(owner->data));
            0 <= owner->len;
        }
        assumption();
    }
    have separate(memory(owner[0..4]), memory(owner->data[0..owner->cap])) by {
        transport(
            at(statement(4).entry, separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->cap])
            )),
            separate(memory(owner[0..4]), memory(owner->data[0..owner->cap]))
        ) using {
            at(statement(4).entry, (index + 1)) < at(statement(4).entry, owner->cap);
            at(statement(5).entry, separate(memory(owner->len), memory(owner->cap)));
            at(statement(5).entry, separate(memory(owner->len), memory(owner->data)));
            at(statement(5).entry, separate(memory(owner->cap), memory(owner->data)));
            at(statement(5).entry, loadable(old(owner->len)));
            at(statement(5).entry, loadable(old(owner->cap)));
            at(statement(5).entry, loadable(old(owner->data)));
            at(statement(5).entry, loadable(old(owner->data[0..owner->cap])));
            at(statement(5).entry, 0) <= at(statement(5).entry, index);
            at(statement(4).entry, index) < at(statement(4).entry, owner->cap);
            at(statement(4).entry, separate(memory(owner[0..4]), memory(owner->data[0..owner->cap])));
            contains(owned_buffer(owner), memory(owner->len));
            contains(owned_buffer(owner), memory(owner->cap));
            contains(owned_buffer(owner), memory(owner->data));
            0 <= owner->len;
            owner->len < owner->cap;
        }
        assumption();
    }
    have owner->cap == old(owner->cap) by {
        have at(statement(4).entry, owner->cap) == old(owner->cap) by {
            normalize();
        }
        transport(
            at(statement(4).entry, owner->cap) == old(owner->cap),
            owner->cap == old(owner->cap)
        ) using {
            at(statement(4).entry, owner->cap) == old(owner->cap);
            at(statement(4).entry, (index + 1)) <
                at(statement(4).entry, owner->cap);
            separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->cap])
            );
        }
        assumption();
    }
    have owner->data == old(owner->data) by {
        have at(statement(4).entry, owner->data) == old(owner->data) by {
            normalize();
        }
        transport(
            at(statement(4).entry, owner->data) == old(owner->data),
            owner->data == old(owner->data)
        ) using {
            at(statement(4).entry, owner->data) == old(owner->data);
            separate(memory(owner->len), memory(owner->cap));
            separate(memory(owner->len), memory(owner->data));
            separate(memory(owner->cap), memory(owner->data));
            contains(owned_buffer(owner), memory(owner->len));
            contains(owned_buffer(owner), memory(owner->cap));
            contains(owned_buffer(owner), memory(owner->data));
            0 <= owner->len;
            owner->len < owner->cap;
            separate(memory(owner[0..4]), memory(owner->data[0..owner->cap]));
            owner->cap == old(owner->cap);
        }
        assumption();
    }
    fold(owned_buffer(owner));
    frame();
    have result == (old(owner->len) + 1) by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 buffer_push_preserves_first(
    struct buffer* owner,
    int32 data[],
    int32 value
) {
    requires 1 <= owner->len;
    requires owner->len + 1 < owner->cap;
    requires owner->data == data;
    owns owned_buffer(owner);
    mutable owner[0..1],
        (owner->data + owner->len)[0..2];

    ensures data[0] == old(data[0]);
} by {
    execute();
    frame();
    have at(statement(1).entry, data[0]) == old(data[0]) by {
        normalize();
    }
    have data[0] == old(data[0]) by {
        transport(
            at(statement(1).entry, data[0]) == old(data[0]),
            data[0] == old(data[0])
        ) using {
            at(statement(1).entry, data[0]) == old(data[0]);
            at(statement(1).entry, 1) <=
                at(statement(1).entry, owner->len);
            at(statement(1).entry, owner->data) ==
                at(statement(1).entry, data);
            at(statement(1).entry, (owner->len + 1)) < at(statement(1).entry, owner->cap);
            at(statement(2).entry, loadable(old(owner->len)));
            at(statement(2).entry, loadable(old(owner->cap)));
            at(statement(2).entry, loadable(old(owner->data)));
            at(statement(2).entry, loadable(old(owner->data[0..owner->cap])));
            at(statement(1).entry, 0) <= at(statement(1).entry, owner->len);
            at(statement(1).entry, owner->len) < at(statement(1).entry, owner->cap);
            0 <= owner->len;
        }
        assumption();
    }
    assumption();
    assumption();
}
```

```expect
pass
```
