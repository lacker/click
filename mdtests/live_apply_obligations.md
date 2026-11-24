# Live theorem application proves premises at the current statement

```c filename=live_apply.c
int increment(int x) { x += 1; return x; }
```

```click
verifying "live_apply.c";
theorem increased(before: int32, after: int32) {
    requires after > before;
    ensures after > before by close();
}
int32 increment(int32 x) {
    requires 0 <= x;
    requires x < 10;
    ensures result > old(x);
} by {
    step();
    apply(increased(old(x), x));
    step();
}
```

```expect
pass
```
