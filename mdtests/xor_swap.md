# XOR swap

The three-assignment XOR swap exchanges two independent scalar values without
a temporary. The proof compares both final parameter values with their
function-entry snapshots. This is not the aliased-memory version of the trick:
using the same storage location for both operands would zero that location.

```c filename=xor_swap.c
int32 xor_swap(int32 x, int32 y) {
    x ^= y;
    y ^= x;
    x ^= y;
    return x;
}
```

```click
verifying "xor_swap.c";

int32 xor_swap(int32 x, int32 y) {
    for statement(3) as swapped {
        assert x == x by auto;
    }

    ensures result == old(y)
        and at(swapped.entry, x) == old(y)
        and at(swapped.entry, y) == old(x) by {
        execute_rest();
        simp();
    }
}
```

```expect
pass
```
