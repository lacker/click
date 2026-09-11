# Matched Integer bindings do not become C values

An Integer constructor field cannot be compared with a machine resource
parameter. The arm keeps the mathematical carrier, so this declaration is
rejected before ownership rewriting.

```c filename=integer_resource_match_binding_rejects_c_mix.c
void keep(int32 bound) { }
```

```click
verifying "integer_resource_match_binding_rejects_c_mix.c";

spec enum Model {
    Empty,
    Value(Integer),
}

resource box(bound: int32) {
    field model: Model;
    match model {
        Model::Empty => { fact 0 == 0; },
        Model::Value(value) => { fact value >= bound; },
    }
}

void keep(int32 bound) {
    owns c: box(bound);
    ensures c.model == old(c.model);
} by {
    unfold(c);
    execute();
    fold(c);
    simp();
}
```

```expect
fail: mathematical Integer expressions cannot be compared with C values
```
