# A callback may not require a differently parameterized token

Abstract token identity includes its arguments.  Ownership of `permit(key)`
cannot satisfy a concrete callback requirement for `permit(other)`.

```c filename=different_callback_token.c
int32 use_other_token(int32 key, int32 other) {
    return key;
}

int32 apply_token(
    int32 (*callback)(int32, int32),
    int32 key,
    int32 other
) {
    return callback(key, other);
}

int32 different_token_caller(int32 key, int32 other) {
    return apply_token(&use_other_token, key, other);
}
```

```click
abstract resource permit(key: int32);

verifying "different_callback_token.c";

contract int32 UseKey(int32 key, int32 other) {
    owns permit(key);
    ensures result == key;
}

int32 use_other_token(int32 key, int32 other) {
    owns permit(other);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 apply_token(
    int32 (*callback)(int32, int32),
    int32 key,
    int32 other
) {
    requires UseKey(callback);
    owns permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 different_token_caller(int32 key, int32 other) {
    owns permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}
```

```expect
fail: function `use_other_token` does not satisfy named contract `UseKey`
```
