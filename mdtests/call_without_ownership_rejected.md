# a function that owns nothing does not preserve caller memory

A contract that declares no resources owns nothing, so its write footprint is
empty. A callee that writes a global must therefore be rejected at its own
contract boundary, rather than letting callers preserve stale values across the
call.

```c filename=call_without_ownership_rejected.c
int32 g = 0;

int32 bump() {
    g = g + 1;
    return 0;
}
```

```click
verifying "call_without_ownership_rejected.c";

int32 bump() {
    requires g < 100;
    ensures result == 0;
}
```

```expect
fail: outside the mutable footprint
```
