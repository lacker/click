# arena destruction requires the empty-arena resource

A live region owns its selected backing interval, so its caller cannot also
hold the whole empty-arena resource required by destruction. Calling the
destructor while only the live-region resource remains must fail at the call.

```c filename=arena_destroy.c
struct arena {
    int32 marker;
};

void arena_destroy(struct arena* arena) {
}
```

```c filename=destroy_with_live_region.c
struct arena {
    int32 marker;
};

struct region {
    int32 marker;
};

void destroy_with_live_region(
    struct arena* arena,
    struct region* region
) {
    arena_destroy(arena);
}
```

```click
abstract resource arena_empty(arena: struct arena*);
abstract resource arena_region(region: struct region*);

verifying "arena_destroy.c";
verifying "destroy_with_live_region.c";

void arena_destroy(struct arena* arena) {
    consumes arena_empty(arena);
}

void destroy_with_live_region(
    struct arena* arena,
    struct region* region
) {
    owns arena_region(region);
}
```

```expect
fail: missing resource fact `owns arena_empty(arena)`
```
