# A C outcome cannot invent conditional evidence

```c filename=normalize_missing.c
int32 identity(int32 x) { return x; }
```

```click
verifying "normalize_missing.c";

int32 identity(int32 x) {
    requires x == 0;
    ensures (if x == 1 { result } else { 7 }) == result;
} by {
    step();
    normalize() using { x == 1; }
}
```

```expect
fail: normalize
```
