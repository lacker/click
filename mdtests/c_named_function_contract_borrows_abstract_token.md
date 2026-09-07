# Callback refinement can borrow an owned abstract token

The named contract preserves ownership, while the concrete callback only
borrows a view.  After the indirect call returns, the caller still owns the
token and can pass it to a consuming function.

```c filename=borrowed_callback_token.c
int32 inspect_token(int32 key) {
    return key;
}

int32 apply_inspect(int32 (*callback)(int32), int32 key) {
    return callback(key);
}

int32 spend_token(int32 key) {
    return key;
}

int32 borrow_then_spend(int32 key) {
    int32 ignored;
    ignored = apply_inspect(&inspect_token, key);
    return spend_token(key);
}
```

```click
abstract resource permit(key: int32);

verifying "borrowed_callback_token.c";

contract int32 Inspect(int32 key) {
    owns permit(key);
    ensures result == key;
}

int32 inspect_token(int32 key) {
    views permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 apply_inspect(int32 (*callback)(int32), int32 key) {
    requires Inspect(callback);
    owns permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 spend_token(int32 key) {
    consumes permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 borrow_then_spend(int32 key) {
    consumes permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}
```

```expect
pass
```
