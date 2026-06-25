# C for loops

This checks the first C0 `for` slice. A loop of the form
`for (i = init; condition; i = step) { body }` is parser sugar for:

```c
i = init;
while (condition) {
    body;
    i = step;
}
```

The first slice intentionally supports only scalar assignment in the initializer
and step. Declarations, omitted clauses, `++`, and `continue` are not part of
this sugar.

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

```click
verifying "for_sum_concrete.c";
verifying "for_count_invariant.c";

int32 for_sum_concrete() {
    ensures sum: result == 3 by auto;
}

int32 for_count_invariant(int32 n) {
    requires n >= 0 and n <= 2147483647;

    loop 0 {
        invariant i >= 0 and i <= n by auto;
    }

    ensures count: result == n by auto;
}
```

```expect
pass
```
