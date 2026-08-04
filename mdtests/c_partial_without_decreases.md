# recursive C contracts remain partial without decreases

This function may recurse forever. Its contract still proves only what is true
if a call returns.

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

int32 stuck(int32 n) {
    ensures result == 0 by auto;
}
```

```expect
pass
```
