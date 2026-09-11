# A const callback table discharges abstract field contracts

`run_suite` is verified against named contracts on its table fields alone, the
way `c_named_function_contract_fields.md` verifies `use_callbacks`: two fields
share a signature and carry different behavior. The caller passes
`&suite`, so each required fact is discharged by concrete formation from the
address the initializer named — `propagate` must refine `Propagate` and `copy`
must refine `Copy`. Binding a field to the other function changes the result,
so the two facts cannot be confused.

```c filename=abstract_table.c
struct callbacks {
    int32 (*propagate)();
    int32 (*copy)();
};

int32 propagate() {
    return 3;
}

int32 copy() {
    return 5;
}

static const struct callbacks suite = {
    .propagate = &propagate,
    .copy = &copy
};

int32 run_suite(const struct callbacks *callbacks) {
    int32 propagated;
    int32 copied;
    propagated = callbacks->propagate();
    copied = callbacks->copy();
    return propagated * 10 + copied;
}

int32 caller() {
    return run_suite(&suite);
}
```

```click
verifying "abstract_table.c";

contract int32 Propagate() {
    ensures result == 3;
}

contract int32 Copy() {
    ensures result == 5;
}

int32 propagate() {
    ensures result == 3 by auto;
}

int32 copy() {
    ensures result == 5 by auto;
}

int32 run_suite(const struct callbacks *callbacks) {
    views object(callbacks);
    requires loadable(callbacks->propagate);
    requires loadable(callbacks->copy);
    requires Propagate(callbacks->propagate);
    requires Copy(callbacks->copy);
    ensures result == 35 by auto;
}

int32 caller() {
    ensures result == 35 by auto;
}
```

```expect
pass
```
