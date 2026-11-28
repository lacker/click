# A loop writing a global breaks an empty write footprint

`walk` declares no writes, but its loop stores to the global `counter`.
The loop runs to its guard-false exit, so the iterations that write
`counter` return to the loop head and lie on no exit's path. The same store
outside a loop is refused at contract closing; inside the loop it used to
verify, because neither the summary facts nor the memory history between
entry and exit recorded what the iterations wrote. The loop rule now records
the iterations' writes on each exit, and closing refuses this one.

```c filename=walk.c
int counter;
int walk(int n) {
    int i = 0;
    while (i < n) { counter = i; i = i + 1; }
    return 0;
}
```

```click
verifying "walk.c";
int32 walk(int32 n) { requires n >= 0; ensures result == 0; } by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
    }
}
```

```expect
fail: write to `&counter` is outside the mutable footprint
```
