# A bare designator stored into a callback field dispatches its target

Storing a function designator into a struct function-pointer field records the
same address `&compare` would, so loading the field back and calling through it
dispatches the known target exactly.

```c filename=c_callback_bare_designator_field_store.c
struct callback_table {
    int32 (*compare)(int32, int32);
};

int32 compare(int32 left, int32 right) {
    return left - right;
}

int32 caller() {
    struct callback_table* table;
    int32 (*callback)(int32, int32);
    int32 result;
    table = malloc(sizeof(struct callback_table));
    if (table == 0) {
        return 0;
    }
    table->compare = compare;
    callback = table->compare;
    result = callback(40, 2);
    free(table);
    return result;
}
```

```click
verifying "c_callback_bare_designator_field_store.c";

int32 compare(int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    ensures result == left - right by auto;
}

int32 caller() {
    ensures result == 0 or result == 38 by auto;
}
```

```expect
pass
```
