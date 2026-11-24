# A contract refines another with value parameters on both

An abstract refinement theorem may relate contracts with value parameters,
each fact fixing its own: from `Adds(f, { amount: 3 })` it concludes
`Shifts(f, { offset: 3 })`. Unfolding both binds `amount` and `offset` to
the facts' values.

```c filename=adds.c
int32 unused(int32 x) {
    return x;
}
```

```click
verifying "adds.c";

contract int32 Adds(int32 x) {
    let amount: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= amount and amount <= 1000;
    ensures result == x + amount;
}

contract int32 Shifts(int32 x) {
    let offset: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= offset and offset <= 1000;
    ensures result == x + offset;
}

theorem adds_three_shifts_three(f: int32 (*)(int32)) {
    requires Adds(f, { amount: 3 });
    ensures Shifts(f, { offset: 3 }) by {
        unfold(Adds(f, { amount: 3 }));
        unfold(Shifts(f, { offset: 3 }));
        close();
    }
}
```

```expect
pass
```
