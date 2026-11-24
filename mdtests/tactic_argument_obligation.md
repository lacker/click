# Tactic argument evaluation has ordinary obligations

```c filename=tactic_argument.c
void make(int32 n) {}
```

```click
verifying "tactic_argument.c";
resource counter() { field next: int32; }
tactic create(n: int32) {
    produces c: counter();
} by {
    let c = fold(counter(), { next: n });
}
void make(int32 n) {
    requires n < 2147483647;
    produces c: counter();
} by {
    let { c: c } = create(n + 1) by { close(); }
}
```

```expect
pass
```
