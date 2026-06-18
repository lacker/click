# Omitted proof clauses use the default prover

This checks the compact Click style where a guarantee ends with `;` instead of
an explicit `by auto;`. The omitted proof clause uses the default prover.

```c filename=default_prover.c
int32 default_prover(int32* p) {
    p[0] = 1;
    return p[0];
}
```

```click
verifying "default_prover.c";

int32 default_prover(int32* p) {
    requires valid_range(p[0..1]);
    mutable p[0..1];
    ensures returns_written: result == 1;
}
```

```expect
pass
```
