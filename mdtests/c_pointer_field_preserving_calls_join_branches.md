# Branch join after pointer-field-preserving modular calls

```c filename=vector.c
struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_get(struct vector* owner, int32 index) {
    int32* data;
    data = owner->data;
    return data[index];
}

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    int32* data;
    data = owner->data;
    data[index] = value;
    return data[index];
}

int32 vector_replace_if(
    struct vector* owner,
    int32 index,
    int32 replacement,
    int32 replace
) {
    int32 original;
    int32 selected;
    original = vector_get(owner, index);
    if (replace != 0) {
        selected = vector_set(owner, index, replacement);
    } else {
        selected = vector_set(owner, index, original);
    }
    return selected;
}
```

```click
resource nonempty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}


verifying "vector.c";

int32 vector_get(struct vector* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views nonempty_vector(owner);

    ensures result == owner->data[index];
    ensures result == old(owner->data[index]);
} by {
    step();
    step();
    step();
    close();
    close();
}

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;
    owns nonempty_vector(owner);
    ensures result == value;
    ensures owner->data[index] == value;
    ensures owner->len == old(owner->len);
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    step();
    step();
    fold(nonempty_vector(owner));
    close();
    close();
    close();
    close();
    close();
    close();
}

int32 vector_replace_if(
    struct vector* owner,
    int32 index,
    int32 replacement,
    int32 replace
) {
    requires 0 <= index;
    requires index < owner->len;
    owns nonempty_vector(owner);

    ensures replace != 0 implies result == replacement;
} by {
    step_until(statement(3).entry);
    branch {
        true => {
            step();
            step();
            have replace != 0 implies selected == replacement;
        }
        false => {
            step();
            step();
            have replace != 0 implies selected == replacement by {
                intro();
                contradiction(not replace != 0);
            }
        }
    }
    step();
    close();
    close();
}
```

```expect
pass
```
