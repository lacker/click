# A modular C pointer-field prefix postcondition survives checked restoration

```c filename=vector.c
struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_push(struct vector* owner, int32 value) {
    int32 index;
    int32* data;
    index = owner->len;
    data = owner->data;
    data[index] = value;
    owner->len = index + 1;
    return owner->len;
}

int32 caller(struct vector* owner, int32 value) { return vector_push(owner, value); }
```

```click
resource vector_storage(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

verifying "vector.c";
int32 vector_push(struct vector* owner, int32 value) {
    requires owner->len < owner->cap;
    owns vector_storage(owner);
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->data[old(owner->len)] == value;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures forall (k: int32) {
        0 <= k and k < old(owner->len) implies
            owner->data[k] == old(owner->data[k])
    };
} by {
    unfold(vector_storage(owner));
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have owner->data == old(owner->data) by {
        simp();
    }
    have owner->data[old(owner->len)] == value by {
        simp();
    }
    fold(vector_storage(owner));
    have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < old(owner->len));
        transport(old(owner->data[k]) == old(owner->data[k]), owner->data[k] == old(owner->data[k])) using {
            at(statement(5).entry, owner->len) <= at(statement(5).entry, owner->cap);
            0 <= k;
            k < old(owner->len);
        }
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 caller(struct vector* owner, int32 value) {
    requires owner->len < owner->cap;
    owns vector_storage(owner);
    ensures forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) };
} by { execute(); assumption(); simp(); }
```

```expect
pass
```
