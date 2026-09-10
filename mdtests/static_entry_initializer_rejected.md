# ordinary function entry does not reset function-local statics

A function-local static has one program-lifetime object. Its initializer is
not reapplied when a function is called again.

```c filename=static_entry_initializer_rejected.c
int32 twice() {
    static int32 calls = 0;
    calls = calls + 1;
    calls = calls + 1;
    return calls;
}
```

```click
verifying "static_entry_initializer_rejected.c";

int32 twice() {
    requires calls < 1000;
    owns &calls[0..1];
    ensures result == old(calls) + 2;
    ensures stale_initializer: result == 2;
}
```

```expect
fail: stale_initializer
```
