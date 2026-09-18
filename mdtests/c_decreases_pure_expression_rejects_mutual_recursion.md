# an expression recursion measure ranks direct self-recursion only

An expression measure is not analysed: the descent is owed as an obligation at
each call to the function that declared the measure. In a two-function cycle
neither call is such a call — `even` calls `odd` and `odd` calls `even` — so
nothing would be ranked and the cycle would be certified with no descent
anywhere. The declaration is refused by name instead.
[`c_decreases_mutual_recursion.md`](c_decreases_mutual_recursion.md) is the
same pair ranked by `decreases n`, whose analysis reads the bodies rather than
the call steps and still handles it.

```c filename=c_decreases_pure_expression_even.c
int32 even(int32 n) {
    int32 result;
    if (n > 0) {
        result = odd(n - 1);
        return result;
    }
    return 1;
}
```

```c filename=c_decreases_pure_expression_odd.c
int32 odd(int32 n) {
    int32 result;
    if (n > 0) {
        result = even(n - 1);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_pure_expression_even.c";
verifying "c_decreases_pure_expression_odd.c";

function level(n: int32) -> int32 {
    n
}

int32 even(int32 n) {
    decreases level(n);
    ensures result >= 0 by auto;
}

int32 odd(int32 n) {
    decreases level(n);
    ensures result >= 0 by auto;
}
```

```expect
fail: recursive component with `odd`
```
