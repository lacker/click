# `decreases` naming a non-parameter name is refused

A `decreases` clause is one expression, classified after resolution (D6): a
declared resource application, a contract resource binder, or an int32
parameter. `m` here is a body local, so it is none of the three and the
clause has nothing to rank.

```c filename=c_decreases_rejects_non_parameter_binder.c
int32 countdown(int32 n) {
    int32 m;

    if (n <= 0) {
        return 0;
    }
    m = n - 1;
    return countdown(m);
}
```

```click
verifying "c_decreases_rejects_non_parameter_binder.c";

int32 countdown(int32 n) {
    requires n >= 0;
    decreases m;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: must name an int32 parameter
```
