# A refinement theorem concludes a contract with value parameters

A refinement theorem may conclude a contract with value parameters, fixing
them as an attachment does: `Adds(&add3, { amount: 3 })`. Its
`unfold(Adds(&add3, { amount: 3 }))` opens the obligation with `amount` bound to `3`.

```c filename=adds.c
int32 add3(int32 x) {
    return x + 3;
}
```

```click
verifying "adds.c";

contract int32 Adds(int32 x) {
    let amount: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= amount and amount <= 1000;
    ensures to_integer(result) == to_integer(x + amount);
}

int32 add3(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures to_integer(result) == to_integer(x + 3);
}

theorem add3_adds_three() {
    ensures Adds(&add3, { amount: 3 }) by {
        unfold(Adds(&add3, { amount: 3 }));
        close();
    }
}
```

```expect
pass
```
