# A termination promise needs its proof

An ordinary nested scope cannot turn an unproved return promise into a fact.

```c filename=termination_ordinary.c
int32 leaf(void) { return 7; }
```

```click
verifying "termination_ordinary.c";
int32 leaf() { ensures result == 7; }
termination by {
    have termination_returns("leaf") by known();
}
```

```expect
fail: `known()` could not close the current goal
```
