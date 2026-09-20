# a call can bind multiple produced resource instances

The output pattern of a call step names every named resource instance the
callee creates. The resources are independent outputs of one C call.

```c filename=split_cells.c
void split_cells(int32* left, int32* right) {
    left[0] = 1;
    right[0] = 2;
}

void caller(int32* left, int32* right) {
    split_cells(left, right);
}
```

```click
resource cell(p: int32*) {
    field value: int32;
    owns p[0..1];
    fact p[0] == value;
}

verifying "split_cells.c";

void split_cells(int32* left, int32* right) {
    consumes left[0..1];
    consumes right[0..1];
    produces first: cell(left);
    produces second: cell(right);
    ensures first.value == 1;
    ensures second.value == 2;
} by {
    execute();
    let first = fold(cell(left), { value: 1 });
    let second = fold(cell(right), { value: 2 });
    simp();
}

void caller(int32* left, int32* right) {
    consumes left[0..1];
    consumes right[0..1];
    produces a: cell(left);
    produces b: cell(right);
    ensures a.value == 1;
    ensures b.value == 2;
} by {
    let { first: a, second: b } = step(split_cells(left, right), {});
    step();
    simp();
}
```

```expect
pass
```
