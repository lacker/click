# a recursive C function verifies against its own partial contract

Recursive calls use the function's contract. This proves safety and the result
when the function returns; it does not assert that every nonnegative input
terminates. The recursive call passes `n` unchanged, so for a positive `n` the
function never returns and the signature says `diverges`.
[`c_decreases_recursive.md`](c_decreases_recursive.md) is the same shape with
`n - 1`, where a `decreases` clause replaces the marker.

```c filename=countdown.c
int32 countdown(int32 n) {
    int32 result;
    if (n <= 0) {
        return 0;
    }
    result = countdown(n);
    return result;
}
```

```click
verifying "countdown.c";

int32 countdown(int32 n) diverges {
    ensures result == 0 by auto;
}
```

```expect
pass
```
