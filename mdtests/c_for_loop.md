# C for loops

This checks the first C0 `for` slice. A loop of the form
`for (i = init; condition; step) { body }` lowers to the existing checked
`while` representation, with both normal completion and `continue` executing
the step before the next condition check:

```c-example
i = init;
while (condition) {
    body;
    step;
}
```

The first slice intentionally supports only scalar assignment in the initializer
and scalar assignment/update statements in the step. Declarations and omitted
clauses remain supported as parser conveniences.

```c filename=for_sum_concrete.c
int32 for_sum_concrete() {
    int32 i;
    int32 total;
    total = 0;
    for (i = 0; i < 3; i = i + 1) {
        total = total + i;
    }
    return total;
}
```

```c filename=for_count_invariant.c
int32 for_count_invariant(int32 n) {
    int32 i;
    for (i = 0; i < n; i = i + 1) {
        i = i;
    }
    return i;
}
```

```c filename=for_continue_concrete.c
int32 for_continue_concrete() {
    int32 i;
    int32 total;
    total = 0;
    for (i = 0; i < 5; i++) {
        if (i == 2) {
            continue;
        }
        total = total + i;
    }
    return total;
}
```

```c filename=for_continue_nested.c
int32 for_continue_nested() {
    int32 i;
    int32 j;
    int32 total;
    total = 0;
    for (i = 0; i < 3; i++) {
        for (j = 0; j < 3; j++) {
            if (j == 1) {
                continue;
            }
            total = total + 1;
        }
    }
    return total;
}
```

```click
verifying "for_sum_concrete.c";
verifying "for_count_invariant.c";
verifying "for_continue_concrete.c";
verifying "for_continue_nested.c";

int32 for_sum_concrete() {
    ensures sum: result == 3 by auto;
}

int32 for_count_invariant(int32 n) {
    requires n >= 0 and n <= 2147483647;
    ensures count: result == n;
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
    }
    step();
    simp();
}

int32 for_continue_concrete() {
    ensures total: result == 8 by auto;
}

int32 for_continue_nested() {
    ensures total: result == 6 by auto;
}
```

```expect
pass
```
