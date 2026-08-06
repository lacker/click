# recursive pure applications remain finite in loop invariants

```c filename=pure_recursive_function_in_invariant.c
int32 count_up(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "pure_recursive_function_in_invariant.c";

function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}

int32 count_up(int32 n) {
    requires n >= 0;
    ensures result == n;
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
        invariant countdown(n) == countdown(n);
    }
    step();
    simp();
}
```

```expect
pass
```
