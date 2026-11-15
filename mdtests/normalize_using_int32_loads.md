# Equal offsets give equal int32 reads in one state

```c filename=int32_loads.c
void keep(int32 p[], int32 n, int32 i, int32 j) { }
```

```click
verifying "int32_loads.c";

void keep(int32 p[], int32 n, int32 i, int32 j) {
    views p[0..n];
    requires 0 <= i;
    requires i < n;
    requires 0 <= j;
    requires j < n;
    requires i == j;
    ensures p[i] == p[j];
} by {
    step_until(function.exit);
    normalize() using { };
}

theorem same_read(p: int32[], n: int32, i: int32, j: int32) {
    views p[0..n];
    requires 0 <= i;
    requires i < n;
    requires 0 <= j;
    requires j < n;
    requires i == j;
    ensures (if p[i] == p[j] { 7 } else { 0 }) == 7 by {
        normalize() using { };
    }
}
```

```expect
pass
```
