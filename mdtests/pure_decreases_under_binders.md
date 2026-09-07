# recursive descent still works inside fold and `let` bodies

The positive half of `pure_decreases_shadowed_binder_rejected.md`. Dropping a
shadowing binder from the descent check must not stop an ordinary recursive
call that appears inside a fold body or after a `let`, where the argument is
still the measure parameter itself.

```c filename=pure_decreases_under_binders.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "pure_decreases_under_binders.c";

function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}

function folded(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { (0..2).fold(0, |acc, k| acc + folded(n - 1)) }
}

function after_let(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { let one: int32 = 1; after_let(n - 1) + one }
}

int32 identity(int32 x) {
    ensures result == x by auto;
}
```

```expect
pass
```
