# A perpetual loop has a partial contract

The invariant proves safety for every finite iteration prefix. The impossible
return does not need to be manufactured merely to certify the function.

```c filename=infinite_loop_partial_contract.c
int32 spin() {
    while (1) {
    }
    return 0;
}
```

```click
verifying "infinite_loop_partial_contract.c";

int32 spin() {
    for loop(0) {
        invariant 0 == 0;
    }

    ensures 0 == 0 by auto;
}
```

```expect
pass
```
