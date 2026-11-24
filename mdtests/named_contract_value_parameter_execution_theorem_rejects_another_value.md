# An execution theorem for one value does not prove another

`add3` adds three, so an execution theorem concluding
`Adds(&add3, { amount: 4 })` is refused: its checked call is proved with
`amount` at `4`.

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

theorem add3_adds_four() executes add3(int32 x) {
    ensures Adds(&add3, { amount: 4 }) by {
        step();
        close();
    }
}
```

```expect
fail: search did not retain a complete proof for `add3_adds_four.ensures_0`
```
