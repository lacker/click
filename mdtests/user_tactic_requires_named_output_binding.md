# A user-defined tactic's single output still needs a named binding

The output pattern names the tactic's `after` slot explicitly, even when
the tactic produces only one resource.

```c filename=user_tactic_requires_named_output_binding.c
void user(int *p) {
}
```

```click
verifying "user_tactic_requires_named_output_binding.c";

resource cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}

tactic rename_cell(p: int32*) {
    consumes before: cell(p);
    produces after: cell(p);
} by {
    unfold(before);
    let after = fold(cell(p), { value: *p });
}

void user(int32* p) {
    consumes input: cell(p);
    produces output: cell(p);
} by {
    let output = rename_cell(p, { before: input });
    step_until(function.exit);
    close();
}
```

```expect
fail: user-defined tactic outputs require named bindings
```
