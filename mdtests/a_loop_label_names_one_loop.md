# A loop label names one loop

`loop label` names the loop the tactic meets, and `at(label.exit, ...)`
reads that loop's exit state. A second `loop label` at a different loop
would make the same name mean two program points, so it is refused. Here
`L` would name both loops, and `at(L.exit, j)` would read 0 at the first
loop's exit and 5 at the second's.

```c filename=two_loops.c
int32 two(int32 i, int32 n, int32 j) {
    while (i < n) {
        i = i + 1;
    }
    while (j < 5) {
        j = j + 1;
    }
    return j;
}
```

```click
verifying "two_loops.c";

int32 two(int32 i, int32 n, int32 j) {
    requires 0 <= i and i <= n;
    requires n < 2147483647;
    requires j == 0;
    ensures at(L.exit, j) == 5;
} by {
    loop L {
        invariant 0 <= i and i <= n and j == 0;
    }
    loop L {
        invariant 0 <= j and j <= 5;
    }
    step();
    close();
}
```

```expect
fail: loop label `L` already names loop(0) on this execution path
```
