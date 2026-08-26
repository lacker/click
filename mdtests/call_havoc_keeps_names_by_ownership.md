# A call's havoc keeps the name of a cell that ownership proves untouched

`store_first` writes `data[0]`; its `ensures data[0] == value` names that
cell under the memory after the call. `touch_box` then writes `owner->value`.
Nothing relates `data` and `owner` except that `backing(data, length)` and
`box(owner)` are two owned resources, so the context proves `touch_box`
cannot touch `data[0]`. Reading `data[0]` at the outcome must resolve to the
same name the earlier fact used: the call-havoc edge froze the context that
proves it, so the assumption-free naming walk crosses it. No `transport` and
no premise list is needed.

```c filename=store_first.c
int32 store_first(int32 data[], int32 length, int32 value) {
    data[0] = value;
    return value;
}
```

```c filename=touch_box.c
struct box {
    int32 value;
};

int32 touch_box(struct box* owner) {
    owner->value = 1;
    return 0;
}
```

```c filename=store_then_touch.c
struct box {
    int32 value;
};

int32 store_then_touch(struct box* owner, int32 data[], int32 length, int32 value) {
    int32 ignored;
    ignored = store_first(data, length, value);
    ignored = touch_box(owner);
    return data[0];
}
```

```click
resource backing(data: int32*, length: int32) {
    owns data[0..length];
    fact 1 <= length;
}

resource box(owner: struct box*) {
    owns owner->value;
}

verifying "store_first.c";
verifying "touch_box.c";
verifying "store_then_touch.c";

int32 store_first(int32 data[], int32 length, int32 value) {
    owns backing(data, length);
    mutable data[0..1];
    ensures result == value;
    ensures data[0] == value;
} by {
    unfold(backing(data, length));
    execute();
    fold(backing(data, length));
    frame();
    simp();
}

int32 touch_box(struct box* owner) {
    owns box(owner);
    mutable owner->value;
    ensures result == 0;
} by {
    unfold(box(owner));
    execute();
    fold(box(owner));
    frame();
    simp();
}

int32 store_then_touch(struct box* owner, int32 data[], int32 length, int32 value) {
    owns backing(data, length);
    owns box(owner);
    mutable owner->value, data[0..1];
    ensures result == value;
} by {
    execute();
    frame();
    have data[0] == value by {
        assumption();
    }
    simp();
}
```

```expect
pass
```
