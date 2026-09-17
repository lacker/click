# recursive C contracts remain partial under `diverges`

This function may recurse forever: the recursive call passes `n` unchanged, so
nothing descends. `diverges` is the honest spelling of that, and the contract
still proves only what is true if a call returns. No `decreases` clause could
be written here, because there is no measure to write.

```c filename=c_partial_without_decreases.c
int32 stuck(int32 n) {
    int32 result;
    if (n > 0) {
        result = stuck(n);
        return result;
    }
    return 0;
}
```

```click
verifying "c_partial_without_decreases.c";

int32 stuck(int32 n) diverges {
    ensures result == 0 by auto;
}
```

```expect
pass
```
