# reversed ranges must not wrap into a readable byte range

```c filename=t.c
int32 negative_view(int32 p[], int32 n) {
    return p[0];
}
```

```click
verifying "t.c";

int32 negative_view(int32 p[], int32 n) {
    requires n == -1073741823;
    views p[0..n];
    ensures result == p[0];
}
```

```expect
fail: assumed a condition fact
```
