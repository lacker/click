# A returned allocation is named `result`

`make` returns the allocation it made. After the return no local holds it,
but the outcome's `result` is exactly that pointer, so the refusal spells it
`result` rather than a report-local `<pointer A>`.

```c filename=a_returned_allocation_is_named_result.c
int32* make(void) {
    int32* p = malloc(8);
    return p;
}
```

```click
verifying "a_returned_allocation_is_named_result.c";

int32* make() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: result == 0; left side evaluated to result, right side evaluated to 0
```
