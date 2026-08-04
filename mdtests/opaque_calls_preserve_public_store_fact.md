# public facts survive several opaque calls

A fact established by one mutating opaque call can be used after several
read-only opaque calls. The generated surface certificate must not expose
call-havoc identities or lose the memory-snapshot transport chain.

```c filename=opaque_calls_preserve_public_store_fact.c
struct box {
    int32 value;
};

int32 make_zero(struct box* box) {
    box->value = 0;
    return 0;
}
```

```c filename=opaque_calls_preserve_public_store_fact_read.c
struct box {
    int32 value;
};

int32 read_zero(struct box* box) {
    return box->value;
}
```

```c filename=opaque_calls_preserve_public_store_fact_pipeline.c
struct box {
    int32 value;
};

int32 zero_pipeline(struct box* box) {
    int32 made;
    int32 first;
    int32 second;
    made = make_zero(box);
    first = read_zero(box);
    second = read_zero(box);
    return second;
}
```

```click
verifying "opaque_calls_preserve_public_store_fact.c";
verifying "opaque_calls_preserve_public_store_fact_read.c";
verifying "opaque_calls_preserve_public_store_fact_pipeline.c";

resource zero_box(box: struct box*) {
    owns box->value;
    fact box->value == 0;
}

int32 make_zero(struct box* box) {
    consumes object(box);
    mutable object(box);
    produces zero_box(box);

    ensures result == 0;
    ensures box->value == 0;
} by {
    execute();
    fold(zero_box(box));
    frame();
    simp();
}

int32 read_zero(struct box* box) {
    views zero_box(box);
    immutable;

    ensures result == 0;
} by {
    observe(zero_box(box));
    execute();
    frame();
    simp();
}

int32 zero_pipeline(struct box* box) {
    consumes object(box);
    mutable object(box);
    produces zero_box(box);

    ensures result == 0;
    ensures box->value == 0;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
