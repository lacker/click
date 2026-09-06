# Struct callback fields retain distinct named contracts

Two fields can have the same C function-pointer signature while carrying
different behavioral contracts. Indirect-call lookup follows the exact loaded
pointer and its explicit contract fact; it does not enumerate functions or
other same-signature contracts.

```c filename=use_callbacks.c
struct callback_table {
    int32 (*add)(int32, int32);
    int32 (*subtract)(int32, int32);
};

int32 use_callbacks(struct callback_table* table, int32 left, int32 right) {
    int32 sum;
    int32 difference;
    sum = table->add(left, right);
    difference = table->subtract(left, right);
    return sum + difference;
}
```

```click
verifying "use_callbacks.c";

contract int32 Addition(int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    requires left <= 1000;
    requires defined(left + right);
    ensures result == left + right;
    ensures 0 <= result;
    ensures result <= 2000;
}

contract int32 Difference(int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    requires left <= 1000;
    requires defined(left - right);
    ensures result == left - right;
    ensures 0 <= result;
    ensures result <= 1000;
}

int32 use_callbacks(struct callback_table* table, int32 left, int32 right) {
    views object(table);
    requires loadable(table->add);
    requires loadable(table->subtract);
    requires Addition(table->add);
    requires Difference(table->subtract);
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    requires left <= 1000;
    requires defined(left + right);
    requires defined(left - right);
    ensures result == (left + right) + (left - right);
} by {
    execute_until(statement(10));
    have c(sum) == left + right by {
        simp();
    }
    have c(difference) == left - right by {
        simp();
    }
    step();
    simp();
}
```

```expect
pass
```
