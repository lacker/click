# Named contracts compose through a callback-table pipeline

This is the vertical contract regression. A composite resource packages three
function-pointer fields with distinct named contracts. Verified helpers borrow
that table, invoke its abstract callbacks, and compose through an outer
pipeline. The final callback mutates a separately owned accumulator while the
callback table remains immutable.

```c filename=contract_pipeline.c
struct accumulator {
    int32 value;
};

struct callback_table {
    int32 (*add)(int32, int32);
    int32 (*subtract)(int32, int32);
    int32 (*store)(struct accumulator*, int32);
};

int32 compute_sum(
    struct callback_table* table,
    int32 left,
    int32 right
) {
    return table->add(left, right);
}

int32 compute_difference(
    struct callback_table* table,
    int32 left,
    int32 right
) {
    return table->subtract(left, right);
}

int32 store_accumulator(
    struct callback_table* table,
    struct accumulator* accumulator,
    int32 value
) {
    return table->store(accumulator, value);
}

int32 run_pipeline(
    struct callback_table* table,
    struct accumulator* accumulator,
    int32 left,
    int32 right
) {
    int32 sum;
    int32 difference;
    int32 status;

    sum = compute_sum(table, left, right);
    difference = compute_difference(table, left, right);
    status = store_accumulator(table, accumulator, sum + difference);
    return accumulator->value + status;
}

```

```click
verifying "contract_pipeline.c";

contract int32 Addition(int32 left, int32 right) {
    requires defined(left + right);
    ensures result == left + right;
}

contract int32 Difference(int32 left, int32 right) {
    requires defined(left - right);
    ensures result == left - right;
}

resource accumulator_cell(accumulator: struct accumulator*) {
    owns accumulator->value;
}

contract int32 Store(
    struct accumulator* accumulator,
    int32 value
) {
    owns accumulator_cell(accumulator);
    mutable accumulator->value;
    ensures result == 0;
    ensures accumulator->value == value;
}

resource callback_suite(table: struct callback_table*) {
    owns table->add;
    owns table->subtract;
    owns table->store;
    fact Addition(table->add);
    fact Difference(table->subtract);
    fact Store(table->store);
}

int32 compute_sum(
    struct callback_table* table,
    int32 left,
    int32 right
) {
    views callback_suite(table);
    requires defined(left + right);
    ensures result == left + right;
} by {
    open(callback_suite(table)) {
        execute();
        simp();
    }
}

int32 compute_difference(
    struct callback_table* table,
    int32 left,
    int32 right
) {
    views callback_suite(table);
    requires defined(left - right);
    ensures result == left - right;
} by {
    open(callback_suite(table)) {
        execute();
        simp();
    }
}

int32 store_accumulator(
    struct callback_table* table,
    struct accumulator* accumulator,
    int32 value
) {
    views callback_suite(table);
    owns accumulator_cell(accumulator);
    requires separate(memory(object(table)), memory(object(accumulator)));
    mutable accumulator->value;
    ensures result == 0;
    ensures accumulator->value == value;
} by {
    open(callback_suite(table)) {
        execute();
        frame();
        simp();
    }
}

int32 run_pipeline(
    struct callback_table* table,
    struct accumulator* accumulator,
    int32 left,
    int32 right
) {
    views callback_suite(table);
    owns accumulator_cell(accumulator);
    requires separate(memory(object(table)), memory(object(accumulator)));
    requires defined(left + right);
    requires defined(left - right);
    requires defined((left + right) + (left - right));
    mutable accumulator->value;
    ensures result == (left + right) + (left - right);
    ensures accumulator->value == result;
} by {
    execute_until(statement(4));
    have c(sum) == left + right by {
        simp();
    }
    execute_until(statement(5));
    have c(difference) == left - right by {
        simp();
    }
    have defined(c(sum) + c(difference)) by {
        rewrite(c(sum) == left + right);
        rewrite(c(difference) == left - right);
        assumption();
    }
    execute();
    frame();
    simp();
}

```

```expect
pass
```
