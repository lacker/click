# Bare theorem application rejects a missing model equality

Without `x.model == y.model`, equality closure must not supply the missing
connection from `shape(z.model) == shape(y.model)` to the requested equality.

```c filename=model_apply.c
void use_models(void) {}
```

```click
verifying "model_apply.c";
spec enum Model { Empty, Node(int32) }
spec enum Shape { Empty, Node }
function shape(m: Model) -> Shape {
    match m { Model::Empty => Shape::Empty, Model::Node(n) => Shape::Node, }
}
resource ghost(id: int32) { field model: Model; }
theorem same_shape(a: Model, b: Model) {
    requires shape(a) == shape(b);
    ensures shape(a) == shape(b) by { close(); }
}
void use_models() {
    owns x: ghost(0);
    owns y: ghost(1);
    owns z: ghost(2);
    requires shape(z.model) == shape(y.model);
    ensures 0 == 0;
} by {
    apply(same_shape(x.model, z.model));
}
```

```expect
fail: theorem `same_shape` has an unproved obligation: `shape(x.model) == shape(z.model)`
```
