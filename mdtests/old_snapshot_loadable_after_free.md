# field-derived old snapshot remains loadable after free

Unfolding a composite can materialize its fields at several harmlessly
different memory snapshots. Retiring the old allocation must not prevent a
postcondition from loading an entry-state element through the original data
field when the entry capacity range covers that element.

```c filename=old_snapshot_loadable_after_free.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 old_snapshot_loadable_after_free(
    struct buffer* owner,
    int32 index
) {
    int32* old_data;
    int32 value;
    old_data = owner->data;
    value = read_old_element(old_data, owner->cap, index);
    free(old_data);
    return value;
}
```

```c filename=read_old_element.c
int32 read_old_element(int32 data[], int32 length, int32 index) {
    return data[index];
}
```

```click
verifying "old_snapshot_loadable_after_free.c";
verifying "read_old_element.c";

resource allocated_buffer(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    contains allocation(owner->data, owner->cap * 4);
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 1 <= owner->cap;
    fact owner->cap <= 536870911;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

int32 read_old_element(int32 data[], int32 length, int32 index) {
    requires 1 <= length;
    requires 0 <= index;
    requires index < length;
    views data[0..length];
    immutable;
    ensures result == data[index] by auto;
}

int32 old_snapshot_loadable_after_free(
    struct buffer* owner,
    int32 index
) {
    requires 0 <= index;
    requires index < owner->len;
    consumes allocated_buffer(owner);
    ensures result == old(owner->data[index]);
} by {
    unfold(allocated_buffer(owner));
    step() using {
        0 <= index;
        index < owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->len), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->cap), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->data), allocation(owner->data, (owner->cap * 4)));
        loadable(owner->len);
        loadable(owner->cap);
        loadable(owner->data);
        loadable(owner->data[0..owner->cap]);
        0 <= owner->len;
        owner->len <= owner->cap;
        1 <= owner->cap;
        owner->cap <= 536870911;
    }
    step() using {
        0 <= index;
        index < owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->len), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->cap), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->data), allocation(owner->data, (owner->cap * 4)));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        0 <= owner->len;
        owner->len <= owner->cap;
        1 <= owner->cap;
        owner->cap <= 536870911;
    }
    step() using {
        0 <= index;
        index < owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->len), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->cap), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->data), allocation(owner->data, (owner->cap * 4)));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        0 <= owner->len;
        owner->len <= owner->cap;
        1 <= owner->cap;
        owner->cap <= 536870911;
    }
    step() using {
        0 <= index;
        index < owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->len), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->cap), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->data), allocation(owner->data, (owner->cap * 4)));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        0 <= owner->len;
        owner->len <= owner->cap;
        1 <= owner->cap;
        owner->cap <= 536870911;
    }
    have value == owner->data[index] by {
        assumption();
    }
    step() using {
        0 <= index;
        index < owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->len), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->cap), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->data), allocation(owner->data, (owner->cap * 4)));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        0 <= owner->len;
        owner->len <= owner->cap;
        1 <= owner->cap;
        owner->cap <= 536870911;
        value == owner->data[index];
    }
    step() using {
        0 <= index;
        index < owner->len;
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->len), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->cap), allocation(owner->data, (owner->cap * 4)));
        separate(memory(owner->data), allocation(owner->data, (owner->cap * 4)));
        separate(allocation(owner->data, (owner->cap * 4)), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        0 <= owner->len;
        owner->len <= owner->cap;
        1 <= owner->cap;
        owner->cap <= 536870911;
        value == owner->data[index];
    }
    simp();
}
```

```expect
pass
```
