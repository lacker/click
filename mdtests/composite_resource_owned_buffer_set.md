# composite resource owned buffer set first

This checks a write into the first cell of a composite-owned backing array. The
unfolded contained write permission authorizes the store, and the proof folds
the buffer back afterward.

```c filename=buffer_set_first.c
struct owner {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_set_first(struct owner* owner, int32 value) {
    int32* data;
    data = owner->data;
    data[0] = value;
    return data[0];
}
```

```click
resource owned_buffer(owner: struct owner*) {
    contains write(owner->len);
    contains write(owner->cap);
    contains write(owner->data);
    contains write((owner->data)[0..1]);
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact 1 <= owner->cap;
    fact disjoint(owner[0..3], (owner->data)[0..1]);
}

verifying "buffer_set_first.c";

int32 buffer_set_first(struct owner* owner, int32 value) {
    requires owned_buffer(owner);

    ensures owned_buffer(owner) by {
        unfold(owned_buffer(owner));
        symbolic_execute();
        fold(owned_buffer(owner));
    }

    ensures result == value by {
        unfold(owned_buffer(owner));
        symbolic_execute();
        fold(owned_buffer(owner));
        simp();
    }
}
```

```expect
pass
```
