# A named contract's value parameter is fixed where the contract is attached

`let amount: int32;` in a named contract's body declares a value parameter.
`Adds(f, { amount: k })` attaches the contract to `f` with `amount` bound to
`k`, so a call through `f` returns its argument plus `k`. Passing `&add3`
with `k == 3` checks `add3`'s contract against `Adds` with `amount == 3`.

```c filename=adds.c
int32 add3(int32 x) {
    return x + 3;
}

int32 apply(int32 (*f)(int32), int32 x, int32 k) {
    int32 result;
    result = f(x);
    return result;
}

int32 caller(int32 x) {
    int32 result;
    result = apply(&add3, x, 3);
    return result;
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

int32 add3(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + 3;
}

int32 apply(int32 (*f)(int32), int32 x, int32 k) {
    requires Adds(f, { amount: k });
    requires 0 <= x and x <= 1000;
    requires 0 <= k and k <= 1000;
    ensures result == x + k;
}

theorem add3_is_adds_three() {
    ensures Adds(&add3, { amount: 3 }) by {
        unfold(Adds(&add3, { amount: 3 }));
        close();
    }
}

int32 caller(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + 3;
} by {
    apply(add3_is_adds_three());
}
```

```expect
pass
```
