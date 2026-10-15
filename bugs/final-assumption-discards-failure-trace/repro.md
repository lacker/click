# Original string clear

```c filename=owned_string_clear.c
struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_clear(struct owned_string* owner) {
    owner->len = 0;
    owner->data[0] = 0;
    return 0;
}

```

```click
verifying "owned_string_clear.c";
predicate terminated_at(data: int32[], length: int32) {
    data[length] == 0
}

resource owned_string(owner: struct owned_string*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    );
}

int32 owned_string_clear(struct owned_string* owner) {
    owns owned_string(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->data[0] == 0;
} by {
    unfold(owned_string(owner));
    step();
    step();
    step();
    have terminated_at(owner->data, owner->len) by auto;
    have 0 <= owner->len;
    have separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    ) by {
        simp();
    }
    fold(owned_string(owner));
    assumption();
    assumption();
    assumption();
    assumption();
}


```

```expect
pass
```
