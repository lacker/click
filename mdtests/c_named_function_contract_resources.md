# Named function contracts transfer resources and effects

An indirect call applies the same resource transition and mutable footprint as
an ordinary verified call. Here the callback consumes one token and mutates
exactly one integer cell.

```c filename=consume_and_store.c
int32 consume_and_store(int32 token, int32* output) {
    output[0] = token;
    return 0;
}
```

```c filename=invoke_consumer.c
int32 invoke_consumer(
    int32 (*callback)(int32, int32*),
    int32 token,
    int32* output
) {
    int32 status;
    status = callback(token, output);
    return status;
}
```

```click
abstract resource available(token: int32);

verifying "consume_and_store.c";
verifying "invoke_consumer.c";

contract int32 Consumer(int32 token, int32* output) {
    consumes available(token);
    consumes output[0..1];
    mutable output[0..1];
    ensures result == 0;
    ensures output[0] == token;
}

int32 consume_and_store(int32 token, int32* output) {
    consumes available(token);
    consumes output[0..1];
    mutable output[0..1];
    ensures result == 0;
    ensures output[0] == token;
} by {
    execute();
    frame();
    simp();
}

int32 invoke_consumer(
    int32 (*callback)(int32, int32*),
    int32 token,
    int32* output
) {
    requires Consumer(callback);
    consumes available(token);
    consumes output[0..1];
    mutable output[0..1];
    ensures result == 0;
    ensures output[0] == token;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
