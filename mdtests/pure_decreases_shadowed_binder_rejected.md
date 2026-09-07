# a binder that shadows the measure cannot carry the recursive descent

A pure function is admitted only when every recursive call strictly decreases
its declared measure. The measure names a parameter, so a fold, `let`, or
match binder that reuses the spelling is a different variable and `f(n - 1)`
under it does not descend.

Accepting one admits an inconsistent definition: this `bad` unrolls to
`bad(1) == bad(1) + 2`, which no `int32` satisfies, and the resulting equation
would be usable in ordinary C proofs.

```c filename=pure_decreases_shadowed_binder_rejected.c
int32 never_one(int32 x) {
    if (x == x + 2) {
        return 1;
    }
    return 0;
}
```

```click
verifying "pure_decreases_shadowed_binder_rejected.c";

function bad(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { (2..3).fold(0, |acc, n| acc + bad(n - 1) + 2) }
}

int32 never_one(int32 x) {
    requires x == bad(1);
    ensures result == 0;
}
```

```expect
fail: must pass a nonnegative decreases measure strictly smaller than `n`
```
