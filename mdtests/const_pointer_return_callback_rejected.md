# Qualified callback returns are explicitly unsupported

```c filename=main.c
const int *view(int *p) { return p; }
int bad(int *p) { const int *(*f)(int *) = &view; return 0; }
```

```click
verifying "main.c";
int bad(int *p) { ensures result == 0; }
```

```expect
fail: const-qualified
```
