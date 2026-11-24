# Loop exit joining preserves the call condition semantics

The condition call creates a lowering temporary only on the body path. The
join must discard that value-only binding without changing the C return.

```c filename=program.c
static inline int always_stop(int x) { return 1; }
int walk(int n) {
    int i = 0;
    while (i < n) { if (always_stop(i)) break; }
    return i;
}
```

```click
verifying "program.c";
int32 walk(int32 n) { requires n >= 0; ensures result == 1; } by {
    step(); step();
    loop {
        decreases n - i;
        invariant i == 0;
        initialize by close();
        maintain by { step(); step(); step(); }
    }
}
```

```expect
fail: left side evaluated to 0, right side evaluated to 1
```
