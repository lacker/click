# execute rest proof step

This checks `execute_rest()`, the clearer name for executing from the current
proof frontier to function exit. At present the only supported frontier is
function entry, so this is equivalent to `symbolic_execute()`.

```c filename=increment.c
int32 increment(int32 x) {
    return x + 1;
}
```

```click
verifying "increment.c";

int32 increment(int32 x) {
    requires x < 2147483647;

    ensures result == x + 1 by {
        execute_rest();
        simp();
    }
}
```

```expect
pass
```
