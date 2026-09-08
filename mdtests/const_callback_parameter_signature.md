# Function pointer parameter qualification is part of signature identity

```c filename=main.c
const int *view(int *p) { p[0] = 7; return p; }
int bad() { const int *(*f)(const int *) = &view; return 0; }
```

```click
verifying "main.c";
int bad() { ensures result == 0; }
```

```expect
fail: signature
```
