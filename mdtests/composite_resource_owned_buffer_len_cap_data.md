# composite resource owned buffer len cap data

This checks a more realistic owned-buffer shape. The composite resource owns
the struct fields plus the backing buffer derived from `owner->data` and
`owner->cap`. A stronger pre-state resource records that there is room to push
one element; after the mutation, the proof folds back to the ordinary
well-formed buffer resource.

```c filename=push_one.c
struct owner {
    int32 len;
    int32 cap;
    int32* data;
};

int32 push_one(struct owner* owner, int32 value) {
    int32 index;
    int32* data;

    index = owner->len;
    data = owner->data;
    data[index] = value;
    owner->len = index + 1;
    return owner->len;
}
```

```click
resource owned_buffer(owner: struct owner*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap]));
}

resource owned_buffer_with_room(owner: struct owner*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap]));
}

verifying "push_one.c";

int32 push_one(struct owner* owner, int32 value) {
    consumes owned_buffer_with_room(owner);

    produces owned_buffer(owner) by {
        unfold(owned_buffer_with_room(owner));
        execute_rest();
        have 0 <= owner->len by {
            derive(0 <= owner->len) using {
                fact at(statement(6).entry, separate(memory(owner->len), memory(owner->cap)));
                fact at(statement(6).entry, separate(memory(owner->len), memory(owner->data)));
                fact at(statement(6).entry, separate(memory(owner->len), memory((owner->data)[0..owner->cap])));
                fact at(statement(6).entry, separate(memory(owner->cap), memory(owner->data)));
                fact at(statement(6).entry, separate(memory(owner->cap), memory((owner->data)[0..owner->cap])));
                fact at(statement(6).entry, separate(memory(owner->data), memory((owner->data)[0..owner->cap])));
                fact at(statement(6).entry, loadable(old(owner->len)));
                fact at(statement(6).entry, loadable(old(owner->cap)));
                fact at(statement(6).entry, loadable(old(owner->data)));
                fact at(statement(6).entry, loadable(old((owner->data)[0..owner->cap])));
                fact at(statement(6).entry, 0) <= at(statement(6).entry, index);
                fact at(statement(6).entry, index) < at(statement(6).entry, owner->cap);
                fact at(statement(6).entry, separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap])));
                fact contains(owned_buffer_with_room(owner), memory(owner->len));
                fact contains(owned_buffer_with_room(owner), memory(owner->cap));
                fact contains(owned_buffer_with_room(owner), memory(owner->data));
                fact contains(owned_buffer_with_room(owner), memory((owner->data)[0..owner->cap]));
            }
        }
        have owner->len <= owner->cap by { simp(); }
        have separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap])) by {
            simp();
        }
        fold(owned_buffer(owner));
    }

    ensures result <= owner->cap by {
        unfold(owned_buffer_with_room(owner));
        execute_rest();
        have 0 <= owner->len by {
            derive(0 <= owner->len) using {
                fact at(statement(6).entry, separate(memory(owner->len), memory(owner->cap)));
                fact at(statement(6).entry, separate(memory(owner->len), memory(owner->data)));
                fact at(statement(6).entry, separate(memory(owner->len), memory((owner->data)[0..owner->cap])));
                fact at(statement(6).entry, separate(memory(owner->cap), memory(owner->data)));
                fact at(statement(6).entry, separate(memory(owner->cap), memory((owner->data)[0..owner->cap])));
                fact at(statement(6).entry, separate(memory(owner->data), memory((owner->data)[0..owner->cap])));
                fact at(statement(6).entry, loadable(old(owner->len)));
                fact at(statement(6).entry, loadable(old(owner->cap)));
                fact at(statement(6).entry, loadable(old(owner->data)));
                fact at(statement(6).entry, loadable(old((owner->data)[0..owner->cap])));
                fact at(statement(6).entry, 0) <= at(statement(6).entry, index);
                fact at(statement(6).entry, index) < at(statement(6).entry, owner->cap);
                fact at(statement(6).entry, separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap])));
                fact contains(owned_buffer_with_room(owner), memory(owner->len));
                fact contains(owned_buffer_with_room(owner), memory(owner->cap));
                fact contains(owned_buffer_with_room(owner), memory(owner->data));
                fact contains(owned_buffer_with_room(owner), memory((owner->data)[0..owner->cap]));
            }
        }
        have owner->len <= owner->cap by { simp(); }
        have separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap])) by {
            simp();
        }
        fold(owned_buffer(owner));
        simp();
    }
}
```

```expect
pass
```
