# A termination promise needs its proof

An ordinary nested scope cannot turn an unproved return promise into a fact.

```c filename=termination_ordinary.c
int32 leaf(void) { return 7; }
```

```click checked-only
verifying "termination_ordinary.c";
int32 leaf() { ensures result == 7; } by {
    step();
    close();
    close();
    close();
    close();
}
termination by {
    have termination_returns("leaf") by close();
}
```

```expect
fail: `known` requires the current goal as an available semantic fact
```
