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
    owns uninitialized(h->target);
    ensures h->target == p;
    ensures defined(h->target);
}
int32 run() {
    ensures result == -1 or result == 0;
} by {
    step(); step();
    if p == 0 {
        step_until(function.exit);
    } else {
        step(); step(); step(); step();
        if h == 0 {
            step_until(function.exit);
        } else {
            step(); step();
            step(put);
            have defined(h->target) by { close(); }
            mark stored;
            step();
            have defined(h->target) by {
                have separate(region(12).footprint, memory(h->target)) by {
                    normalize() using {};
                }
                preserve(memory(h->target), region(12));
            }
            mark declared;
            step();
            have defined(h->target) by {
                have separate(region(13).footprint, memory(h->target)) by {
                    normalize() using {};
                }
                preserve(memory(h->target), region(13));
            }
            step_until(function.exit);
        }
    }
}
```

```expect
fail: `ensures
```
