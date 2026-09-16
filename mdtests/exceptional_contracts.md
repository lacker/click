# exceptional contract families

This checks that a function can publish distinct normal and exceptional
postcondition families. The C body returns normally, so its exceptional
guarantee is vacuous for this implementation.

```c filename=exceptional_contracts.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "exceptional_contracts.c";

int32 identity(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
```

```expect
pass
```
