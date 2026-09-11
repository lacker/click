# Matched resources preserve mathematical constructor bindings

The selected resource arm binds an `Integer` constructor field as a checked
logical value. Unfold and fold use the constructor evidence and retain the
resource's field exactly.

```c filename=integer_resource_match_binding.c
void keep(void) { }
```

```click
verifying "integer_resource_match_binding.c";

spec enum Model {
    Empty,
    Value(Integer),
}

resource box() {
    field model: Model;
    match model {
        Model::Empty => { fact 0 == 0; },
        Model::Value(value) => { fact value >= 0; },
    }
}

void keep() {
    owns c: box();
    requires c.model == Model::Value(7);
    ensures c.model == old(c.model);
} by {
    unfold(c);
    execute();
    fold(c);
    simp();
}
```

```expect
pass
```
