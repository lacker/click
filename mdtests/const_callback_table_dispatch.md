# A file-scope const callback table dispatches exactly

Linux declares `static const struct rb_augment_callbacks dummy_callbacks = {
.propagate = dummy_propagate, ... };` and passes `&dummy_callbacks`. A load of
such a field yields the concrete function address the initializer named, so
the indirect call dispatches to exactly that function with no contract. The
same holds through a pointer the verifier knows is `&table`, whether that is a
local pointer or an inlined helper's parameter.

Each callback is called on its own arguments, so every swapped binding changes
the total: `11 + 19 + 35` here, against `5 + 21 + 35`, `24 + 19 + 12`, and
`11 + 20 - 2` for the three transpositions.

```c filename=callback_table.c
struct callbacks {
    int32 (*add)(int32, int32);
    int32 (*subtract)(int32, int32);
    int32 (*multiply)(int32, int32);
};

int32 add(int32 left, int32 right) {
    return left + right;
}

int32 subtract(int32 left, int32 right) {
    return left - right;
}

int32 multiply(int32 left, int32 right) {
    return left * right;
}

static const struct callbacks table = {
    .add = &add,
    .subtract = &subtract,
    .multiply = &multiply
};

static inline int32 apply_subtract(const struct callbacks *callbacks,
                                   int32 left, int32 right) {
    return callbacks->subtract(left, right);
}

int32 through_table() {
    int32 sum;
    int32 difference;
    int32 product;
    sum = table.add(8, 3);
    difference = table.subtract(20, 1);
    product = table.multiply(5, 7);
    return sum + difference + product;
}

int32 through_pointer() {
    const struct callbacks *callbacks;
    int32 sum;
    int32 difference;
    int32 product;
    callbacks = &table;
    sum = callbacks->add(8, 3);
    difference = callbacks->subtract(20, 1);
    product = callbacks->multiply(5, 7);
    return sum + difference + product;
}

int32 through_parameter() {
    return apply_subtract(&table, 20, 1);
}
```

```click
verifying "callback_table.c";

int32 add(int32 left, int32 right) {
    requires defined(left + right);
    ensures result == left + right by auto;
}

int32 subtract(int32 left, int32 right) {
    requires defined(left - right);
    ensures result == left - right by auto;
}

int32 multiply(int32 left, int32 right) {
    requires defined(left * right);
    ensures result == left * right by auto;
}

int32 through_table() {
    ensures result == 65 by auto;
}

int32 through_pointer() {
    ensures result == 65 by auto;
}

int32 through_parameter() {
    ensures result == 19 by auto;
}
```

```expect
pass
```
