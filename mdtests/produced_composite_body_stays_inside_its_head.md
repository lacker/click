# A produced composite keeps its body inside its head

After `make_zero` produces `zero_box(box)`, the caller holds the head and
nothing else: the body `box->value` is inside it. A store through the body
without unfolding has no owner, so the written step is refused. Before 2026-09-13 the verified-rule path
installed the body as owned memory beside the head, so this pipeline
verified `result == 0` while the program returns 5.

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
    box->value = 5;
    first = read_zero(box);
    second = first;
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
    consumes *box;
    produces zero_box(box);

    ensures result == 0;
    ensures box->value == 0;
} by {
    step_until(function.exit);
    fold(zero_box(box));
    close();
}

int32 read_zero(struct box* box) {
    views zero_box(box);

    ensures result == 0;
} by {
    observe(zero_box(box));
}

int32 zero_pipeline(struct box* box) {
    consumes *box;
    produces zero_box(box);

    ensures result == 0;
    ensures box->value == 0;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
}
```

```expect
fail: missing resource fact `owns *box`
```
