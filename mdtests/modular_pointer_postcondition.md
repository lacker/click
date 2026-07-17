# Modular calls expose pointer postconditions

A verified call adds pointer-valued postconditions to the caller's pure facts.
The caller can cite that fact explicitly after advancing past the call.

```c filename=set_pointer.c
struct holder {
    int32* data;
};

int32 set_pointer(struct holder* owner, int32* data) {
    owner->data = data;
    return 0;
}
```

```c filename=call_set_pointer.c
struct holder {
    int32* data;
};

int32 call_set_pointer(struct holder* owner, int32* data) {
    int32 ignored;
    ignored = set_pointer(owner, data);
    return owner->data == data;
}
```

```click
verifying "set_pointer.c";
verifying "call_set_pointer.c";

int32 set_pointer(struct holder* owner, int32* data) {
    consumes owner[0..2];
    mutable owner[0..2];
    produces owner[0..2];
    ensures result == 0;
    ensures owner->data == data;
} by {
    execute_rest();
    frame();
    simp();
}

int32 call_set_pointer(struct holder* owner, int32* data) {
    consumes owner[0..2];
    mutable owner[0..2];
    produces owner[0..2];
    ensures result == 1;
} by {
    execute_until(statement(2));
    have owner->data == data by {
        simp();
    }
    execute_rest();
    frame();
    simp();
}
```

```expect
pass
```
