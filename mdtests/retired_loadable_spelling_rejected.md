# the retired `loadable(...)` spelling is refused by name

The memory-range fact is spelled `viewable(...)`, after the `views` clause it
shadows. There is no compatibility alias, so a sidecar still written against
the old spelling is refused where it is parsed, and the refusal names the
replacement instead of reporting an unknown call.

```c filename=retired_loadable_spelling.c
int32 first(int32* p) {
    return p[0];
}
```

```click
verifying "retired_loadable_spelling.c";

int32 first(int32* p) {
    requires loadable(p[0..1]);
    views p[0..1];
    ensures result == p[0] by auto;
}
```

```expect
fail: `loadable(...)` was renamed `viewable(...)`
```
