# A heap pointer field cannot prove the wrong comparison result

The same modular pointer store must not make the caller context
inconsistent and thereby certify a false result.

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
    ensures result == -1 or result == 0;
} by { execute(); simp(); }
```

```expect
fail: `ensures
```
