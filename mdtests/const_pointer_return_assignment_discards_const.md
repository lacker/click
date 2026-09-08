# A call assignment cannot erase return qualification

```c filename=main.c
const int *view(int *p) { return p; }
int *bad(int *p) { int *q = p; q = view(p); return q; }
```

```click
verifying "main.c";
int *bad(int *p) { ensures result == p; }
```

```expect
fail: const qualification
```
