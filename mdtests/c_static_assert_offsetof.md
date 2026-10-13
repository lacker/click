# Static assertions check C constants and offsetof uses padded ABI layout

```c filename=layout.c
struct node { int32 key; };
struct item { char prefix; struct node rb; long count; };
typedef struct item item_t;
_Static_assert(__builtin_offsetof(item_t, rb) == 4, "embedded node offset");
_Static_assert(__builtin_offsetof(item_t, count) == 8, "aligned count offset");

uint64 offset() {
    uint64 result = __builtin_offsetof(struct item, rb);
    result = result + __builtin_offsetof(struct item, count);
    return result;
}
int32 compatible(struct node* p) {
    _Static_assert(__builtin_types_compatible_p(typeof(*p), typeof(((struct item*)0)->rb)) ||
        __builtin_types_compatible_p(typeof(*p), void), "pointer type mismatch in container_of()");
    return 1;
}
```

```click
verifying "layout.c";
uint64 offset() { ensures result == 12u64; } by { execute(); normalize(); }
int32 compatible(struct node* p) { ensures result == 1; } by { execute(); normalize(); }
```

```expect
pass
```
