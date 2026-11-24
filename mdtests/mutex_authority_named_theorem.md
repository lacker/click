# A theorem cannot introduce a primitive name without checked alias transport

```click
theorem keep(mu: void*) {
    consumes guard: mutex_guard(mu);
    ensures 0 == 0 by close();
}
```

```expect
fail: named mutex_guard is currently supported only in C function contracts
```
