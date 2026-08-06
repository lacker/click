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
    ensures 0 == 0;
} by {
    loop {
        invariant 0 == 0;
        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    simp();
}
```

```expect
pass
```
