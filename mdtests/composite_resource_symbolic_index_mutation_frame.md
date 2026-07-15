# composite resource symbolic index mutation frame

This checks that a write through a symbolic backing-array index preserves
separate vector metadata. The index bounds place the write inside the backing
resource, while `separate` keeps that write disjoint from the owner fields, so
the same composite resource can be refolded without re-proving its unchanged
metadata facts.

```c filename=vector_set.c
struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    int32* data;
    data = owner->data;
    data[index] = value;
    return data[index];
}
```

```click
resource vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(owner[0..4]), memory((owner->data)[0..owner->cap]));
}

verifying "vector_set.c";

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;

    owns vector(owner) by {
        unfold(vector(owner));
        execute_rest();
        fold(vector(owner));
    }

    ensures result == value by {
        unfold(vector(owner));
        execute_rest();
        fold(vector(owner));
        simp();
    }
}
```

```expect
pass
```
