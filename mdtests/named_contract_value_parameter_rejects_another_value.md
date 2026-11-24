# A function meets a parameterized contract only for the values it implements

`add3` adds 3, so `Adds(&add3, { amount: 4 })` does not hold, and the call
passing `&add3` with `k == 4` cannot establish `apply`'s requirement.

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
    result = apply(&add3, x, 4);
    return result;
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

int32 apply(int32 (*f)(int32), int32 x, int32 k) {
    requires Adds(f, { amount: k });
    requires 0 <= x and x <= 1000;
    requires 0 <= k and k <= 1000;
    ensures to_integer(result) == to_integer(x + k);
}

theorem add3_is_adds_three() {
    ensures Adds(&add3, { amount: 3 }) by { unfold(Adds(&add3, { amount: 3 })); close(); }
}

int32 caller(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures to_integer(result) == to_integer(x + 4);
} by { apply(add3_is_adds_three()); }
```

```expect
fail: unproved obligation: `Adds(&add3, 4)`
```
