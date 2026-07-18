# simple statement transition

`step()` advances one statement using only exact prerequisites and performs no
automatic proof-context search.

```c filename=simple_statement_step.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "simple_statement_step.c";

int32 identity(int32 x) {
    ensures result == x;
} by {
    step();
    normalize();
}
```

```expect
pass
```
