# A field callback result cannot be assigned to a mutable pointer

```c filename=main.c
struct reader { const int *(*view)(int *); };
int bad(struct reader *r, int *p) { int *q = p; q = r->view(p); return 0; }
```

```click
verifying "main.c";
int bad(struct reader *r, int *p) { ensures result == 0; }
```

```expect
fail: const
```
