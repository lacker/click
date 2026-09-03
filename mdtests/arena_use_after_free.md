# an arena region cannot be used after free

An arena free consumes the unique region authority. A later operation that
requires that authority must fail, which is the resource-level form of a use
after free.

```c filename=arena_read.c
struct region {
    int32 marker;
};

int32 arena_read(struct region* region) {
    return 0;
}
```

```c filename=arena_free.c
struct region {
    int32 marker;
};

void arena_free(struct region* region) {
}
```

```c filename=arena_use_after_free.c
struct region {
    int32 marker;
};

int32 arena_use_after_free(struct region* region) {
    int32 value;
    arena_free(region);
    value = arena_read(region);
    return value;
}
```

```click
abstract resource arena_region(region: struct region*);

verifying "arena_read.c";
verifying "arena_free.c";
verifying "arena_use_after_free.c";

int32 arena_read(struct region* region) {
    consumes arena_region(region);

    produces arena_region(region) by auto;
}

void arena_free(struct region* region) {
    consumes arena_region(region);
}

int32 arena_use_after_free(struct region* region) {
    consumes arena_region(region);

    ensures result == 0 by auto;
}
```

```expect
fail: missing resource fact `owns arena_region(region)`
```
