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
    execute();
    simp();
}
```

```expect
pass
```
