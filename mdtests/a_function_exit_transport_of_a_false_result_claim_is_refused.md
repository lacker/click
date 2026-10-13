# A function-exit transport of a false `result` claim is refused

`is_less` returns 0 on one path, so `result == 1` does not hold at function
exit on every path, and its transport from there is refused.

```c filename=false_exit_claim.c
int32 is_less(uint32 a, uint32 b) {
    return a < b;
}
```

```click
verifying "false_exit_claim.c";

int32 is_less(uint32 a, uint32 b) {
    ensures result == 0 or result == 1;
} by {
    execute();
    have result == 1 by {
        transport(at(function.exit, result == 1), result == 1) using {
        }
    }
    assumption();
}
```

```expect
fail: `transport using` requires a source derivable from its explicit facts
```
