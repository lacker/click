# A nested call cannot pass a const result to a mutable pointer parameter

```c filename=main.c
const int *view(int *p) { return p; }
int read(int *p) { return p[0]; }
int bad(int *p) { return read(view(p)); }
```

```click
verifying "main.c";
int bad(int *p) { ensures result == 0; }
```

```expect
fail: const qualification
```
