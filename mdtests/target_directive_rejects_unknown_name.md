# An unknown target name is rejected with the accepted spellings

The `target` directive selects one of the verifier's own C implementation
targets. An unrecognized name is a sidecar error that lists what is accepted,
not a silently ignored directive.

```c filename=answer.c
int32_t answer(void) {
    return 1;
}
```

```click
target "x86_64-linux-embedded";
verifying "answer.c";

int32 answer() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: unknown C target `x86_64-linux-embedded`; accepted targets are `x86_64-linux-kernel`, `x86_64-linux-userspace`
```
