# a symbolic recursive call unfolds one equation

Unknown-depth recursion remains an opaque application after the first defining
equation. Repeating the same call therefore yields the same finite symbolic
term rather than consuming an evaluator recursion budget.

```c filename=pure_recursive_function_unfold.c
int32 keep(int32 n) {
    return n;
}
```

```click
verifying "pure_recursive_function_unfold.c";

function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}

int32 keep(int32 n) {
    ensures countdown(n) == countdown(n) by auto;
}
```

```expect
pass
```
