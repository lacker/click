# Explicit application of a named contract

Proof parameters and the C signature are separate. This contract declares no
proof parameters, so its application supplies exactly zero arguments.

```c filename=invoke.c
int32 invoke(int32 (*callback)(int32), int32 x) {
    return callback(x);
}
```

```click
verifying "invoke.c";

contract Identity() for int32(int32 x) {
    ensures result == x;
}

int32 invoke(int32 (*callback)(int32), int32 x) {
    requires Identity(callback);
    ensures result == x;
} by {
    step(Identity());
    execute();
    simp();
}
```

```expect
pass
```
