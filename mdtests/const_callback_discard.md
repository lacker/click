# A callback result cannot initialize a mutable view

```c filename=main.c
int bad(const int *(*f)(int *), int *p) { int *q = f(p); return 0; }
```

```click
verifying "main.c";
int bad(const int *(*f)(int *), int *p) { ensures result == 0; }
```

```expect
fail: const
```
