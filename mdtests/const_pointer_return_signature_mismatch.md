# Sidecars must retain return qualification

```c filename=main.c
const int *view(int *p) { return p; }
```

```click
verifying "main.c";
int *view(int *p) { ensures result == p; }
```

```expect
fail: return pointee const
```
