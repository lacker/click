# A callback must preserve a token its named contract preserves

Both interfaces can receive the token, but the concrete callback consumes it
instead of returning it.  It therefore cannot implement a contract that
promises ownership back to the caller.

```c filename=consumed_callback_token.c
int32 consume_token(int32 key) {
    return key;
}

int32 apply_token(int32 (*callback)(int32), int32 key) {
    return callback(key);
}

int32 consumed_token_caller(int32 key) {
    return apply_token(&consume_token, key);
}
```

```click
abstract resource permit(key: int32);

verifying "consumed_callback_token.c";

contract int32 PreserveToken(int32 key) {
    owns permit(key);
    ensures result == key;
}

int32 consume_token(int32 key) {
    consumes permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 apply_token(int32 (*callback)(int32), int32 key) {
    requires PreserveToken(callback);
    owns permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 consumed_token_caller(int32 key) {
    owns permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}
```

```expect
fail: function `consume_token` does not satisfy named contract `PreserveToken`
```
