# Pointer fields can refer to another heap allocation

A pointer loaded from one heap allocation is not constrained to point inside
that allocation. A modular store contract identifies its actual target.

```c filename=heap_pointer.c
struct holder { int32* target; };
void put(struct holder* h, int32* p) { h->target = p; }
int32 run() {
    int32* p = malloc(sizeof(int32));
    if (p == 0) { return -1; }
    struct holder* h = malloc(sizeof(struct holder));
    if (h == 0) { free(p); return -1; }
    put(h, p);
    int32 result = 0;
    if (h->target == p) { result = 1; }
    free(h);
    free(p);
    return result;
}
```

```click
verifying "heap_pointer.c";
void put(struct holder* h, int32* p) {
    owns &h->target;
    ensures h->target == p;
    ensures defined(h->target);
} by { execute(); simp(); }
int32 run() {
    ensures result == -1 or result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
