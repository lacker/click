# A mutable return cannot discard a const parameter

```c filename=main.c
int *bad(const int *p) { return p; }
```

```click
verifying "main.c";
int *bad(const int *p) { ensures result == p; }
```

```expect
fail: const qualification
```
