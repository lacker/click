# Callback refinement can borrow an owned folded composite

The named contract preserves composite ownership, while the concrete callback
only borrows a view. After the indirect call returns, the caller still owns
the folded bundle and can pass it to a consuming function.

```c filename=borrowed_callback_composite.c
int32 inspect_bundle(int32 key) {
    return key;
}

int32 apply_inspect(int32 (*callback)(int32), int32 key) {
    return callback(key);
}

int32 spend_bundle(int32 key) {
    return key;
}

int32 borrow_then_spend_bundle(int32 key) {
    int32 ignored;
    ignored = apply_inspect(&inspect_bundle, key);
    return spend_bundle(key);
}
```

```click
abstract resource permit(key: int32);

resource bundle(key: int32) {
    contains permit(key);
}

verifying "borrowed_callback_composite.c";

contract int32 InspectBundle(int32 key) {
    owns bundle(key);
    ensures result == key;
}

int32 inspect_bundle(int32 key) {
    views bundle(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 apply_inspect(int32 (*callback)(int32), int32 key) {
    requires InspectBundle(callback);
    owns bundle(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 spend_bundle(int32 key) {
    consumes bundle(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 borrow_then_spend_bundle(int32 key) {
    consumes bundle(key);
    ensures result == key;
} by {
    execute();
    simp();
}
```

```expect
pass
```
