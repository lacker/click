# Repeated identical loops keep separate verified rules

The two `while` statements are written identically and are reached from the same
symbolic entry state, so both verified loop rules live in one environment when
either loop is applied. Each rule is still chosen for its own loop: a loop's
invariant checks carry that loop's index, so the two rules never share a loop
statement, and each rule's recorded assumptions have to be exactly available
where it is applied.

```c filename=repeated_loop.c
int32 repeated_loop(int32 n) {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "repeated_loop.c";

int32 repeated_loop(int32 n) {
    ensures result == 3;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= 3;
    }
    step();
    loop {
        invariant i >= 0;
        invariant i <= 3;
    }
    step();
    simp();
}
```

```expect
pass
```
