# A C local named result remains distinct from the contract result

`c(result)` names the C local even though bare `result` denotes the function's
return value in a contract. The local survives an opaque read call and a later
call that mutates the same composite resource.

```c filename=result_box_read.c
struct result_box {
    int32 value;
};

int32 result_box_read(struct result_box* owner) {
    return owner->value;
}
```

```c filename=result_box_write.c
struct result_box {
    int32 value;
};

int32 result_box_write(struct result_box* owner, int32 value) {
    owner->value = value;
    return value;
}
```

```c filename=result_box_pipeline.c
struct result_box {
    int32 value;
};

int32 result_box_pipeline(struct result_box* owner) {
    int32 result;
    int32 ignored;
    result = result_box_read(owner);
    ignored = result_box_write(owner, result);
    return result;
}
```

```click
resource result_box(owner: struct result_box*) {
    owns owner->value;
}

verifying "result_box_read.c";
verifying "result_box_write.c";
verifying "result_box_pipeline.c";

int32 result_box_read(struct result_box* owner) {
    views result_box(owner);
    immutable;
    ensures result == owner->value;
} by {
    observe(result_box(owner));
    execute();
    frame();
    simp();
}

int32 result_box_write(struct result_box* owner, int32 value) {
    owns result_box(owner);
    mutable owner->value;
    ensures result == value;
    ensures owner->value == value;
} by {
    unfold(result_box(owner));
    execute();
    frame();
    fold(result_box(owner));
    simp();
}

int32 result_box_pipeline(struct result_box* owner) {
    owns result_box(owner);
    mutable owner->value;
    ensures result == old(owner->value);
    ensures owner->value == result;
} by {
    execute();
    have at(statement(4).entry, c(result)) == old(owner->value) by simp;
    frame();
    simp();
}
```

```expect
pass
```
