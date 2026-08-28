# execute rest tactic

This checks `execute()`, the clearer name for executing from the current
execution frontier to function exit. From function entry, this is equivalent to
the deprecated `execute()` spelling.

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
        execute();
        simp();
    }
}
```

```expect
pass
```
