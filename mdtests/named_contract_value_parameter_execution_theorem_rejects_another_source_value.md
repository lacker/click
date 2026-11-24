# An execution theorem keeps each fact's own value

From `Adds(f, { amount: 3 })` an execution theorem cannot conclude
`Shifts(f, { offset: 2 })`: the call through `f` returns its argument plus
three, and the target's `offset` is pinned to `2`.

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
    ensures result == x + amount;
}

contract int32 Shifts(int32 x) {
    let offset: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= offset and offset <= 1000;
    ensures result == x + offset;
}

int32 add3(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + 3;
}

theorem adds_three_shifts_two(f: int32 (*)(int32)) executes f(int32 x) {
    requires Adds(f, { amount: 3 });
    ensures Shifts(f, { offset: 2 }) by {
        step(Adds);
        close();
    }
}
```

```expect
fail: search did not retain a complete proof for `adds_three_shifts_two.ensures_0`
```
