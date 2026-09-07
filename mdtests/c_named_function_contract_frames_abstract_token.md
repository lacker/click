# Callback refinement frames abstract tokens the implementation does not need

The named contract preserves two abstract capabilities.  The concrete
callback needs and returns only the first, so the second remains in the frame
around the concrete transition.

```c filename=framed_callback_token.c
int32 keep_first(int32 key, int32 spare) {
    return key;
}

int32 apply_keep(
    int32 (*callback)(int32, int32),
    int32 key,
    int32 spare
) {
    return callback(key, spare);
}

int32 framed_token_caller(int32 key, int32 spare) {
    return apply_keep(&keep_first, key, spare);
}
```

```click
abstract resource permit(key: int32);

verifying "framed_callback_token.c";

contract int32 PreservePair(int32 key, int32 spare) {
    owns permit(key);
    owns permit(spare);
    ensures result == key;
}

int32 keep_first(int32 key, int32 spare) {
    owns permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 apply_keep(
    int32 (*callback)(int32, int32),
    int32 key,
    int32 spare
) {
    requires PreservePair(callback);
    owns permit(key);
    owns permit(spare);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 framed_token_caller(int32 key, int32 spare) {
    owns permit(key);
    owns permit(spare);
    ensures result == key;
} by {
    execute();
    simp();
}
```

```expect
pass
```
