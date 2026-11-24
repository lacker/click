# A failed composite body fact keeps its source spelling

```c filename=a.c
struct box {
    int32 value;
};

int32 make_zero(struct box* box) {
    box->value = 0;
    return 0;
}

int32 read_zero(struct box* box) {
    return box->value;
}

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
verifying "a.c";

resource zero_box(box: struct box*) {
    owns box->value;
    fact box->value == 0;
}

int32 make_zero(struct box* box) {
    consumes *box;
    produces zero_box(box);
    ensures result == 0;
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
} by {
    step();
    step();
    step();
    step();
    unfold(zero_box(box));
    step();
    step();
}
```

```expect
fail: box->value == 0
```
