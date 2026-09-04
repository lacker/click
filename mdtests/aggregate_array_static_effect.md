# aggregate array static writes require an authorized field effect

A function-local static array of structs is external memory for effect
certification. Writing one indexed field without authorizing that field
remains an error.

```c filename=aggregate_array_static_effect.c
struct entry {
    int32 value;
};

int32 increment() {
    static struct entry entries[2];
    entries[1].value = entries[1].value + 1;
    return entries[1].value;
}
```

```click
verifying "aggregate_array_static_effect.c";

int32 increment() {
    immutable;
    ensures result == old(entries[1].value) + 1 by auto;
}
```

```expect
fail: outside the mutable footprint
```
