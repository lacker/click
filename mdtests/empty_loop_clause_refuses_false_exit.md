# An empty loop rule retains its actual exit

The same checked loop can return 1, so its empty clause cannot prove a
postcondition claiming that the return value is 2.

```c filename=r.c
int poll(int x) { return x; }
int spin(int x) {
    while (poll(x) == 0) { }
    return 1;
}
```

```click
verifying "r.c";
int32 poll(int32 x) {
    ensures result == x;
} by { step(); close(); }
int32 spin(int32 x) diverges {
    ensures result == 2;
} by {
    loop diverges { }
    step();
    close();
}
```

```expect
fail: checked outcome `close`
```
