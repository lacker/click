# A contract does not refine another at a different value

`Adds(f, { amount: 3 })` does not give `Shifts(f, { offset: 2 })`: unfolding
both binds `amount` to `3` and `offset` to `2`, and the obligation is
refused.

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
    ensures to_integer(result) == to_integer(x + amount);
}

contract int32 Shifts(int32 x) {
    let offset: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= offset and offset <= 1000;
    ensures to_integer(result) == to_integer(x + offset);
}

theorem adds_three_shifts_two(f: int32 (*)(int32)) {
    requires Adds(f, { amount: 3 });
    ensures Shifts(f, { offset: 2 }) by {
        unfold(Adds(f, { amount: 3 }));
        unfold(Shifts(f, { offset: 2 }));
        close();
    }
}
```

```expect
fail: could not establish `0 <= x and x <= 1000 and (0 <= 2 and 2 <= 1000) implies 0 <= x and x <= 1000 and (0 <= 3 and 3 <= 1000) and ((to_integer((x as int32)) + 3) <= 2147483647 and (to_integer((x as int32)) + 3) >= -2147483648 and to_integer(result) == to_integer((x + 3)) implies (to_integer((x as int32)) + 2) <= 2147483647 and (to_integer((x as int32)) + 2) >= -2147483648 and to_integer(result) == to_integer((x + 2)))`
```
