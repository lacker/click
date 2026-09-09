# A callback result cannot be written through

```c filename=main.c
int bad(const int *(*f)(int *), int *p) { const int *q = f(p); q[0] = 7; return 0; }
```

```click
verifying "main.c";
int bad(const int *(*f)(int *), int *p) { ensures result == 0; }
```

```expect
fail: const
```
