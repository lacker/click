# Direct calls through struct callback fields

```c filename=struct_function_pointer_field_direct_call.c
struct callback_table {
    int32 (*compare)(int32, int32);
};

int32 compare(int32 left, int32 right) {
    return left - right;
}

int32 caller() {
    struct callback_table* table;
    int32 result;
    table = malloc(sizeof(struct callback_table));
    if (table == 0) {
        return 0;
    }
    table->compare = &compare;
    result = table->compare(40, 2);
    free(table);
    return result;
}
```

```click
verifying "struct_function_pointer_field_direct_call.c";

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
