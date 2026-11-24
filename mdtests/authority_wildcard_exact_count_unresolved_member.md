# A helper cannot assume another index is unaffected

```c filename=exact_count_unresolved.c
void inspect(int32* pool, int32* p, int32* q) {}
```

```click
authorized resource slot(pool: int32*, p: int32*) {}
verifying "exact_count_unresolved.c";
void inspect(int32* pool, int32* p, int32* q) {
    owns authority(slot(pool, _));
    consumes slot(pool, p);
} by {
    unfold(slot(pool, p));
    have count(slot(pool, q)) == 0 by close();
}
```

```expect
fail: count(...) requires resolved member indices or the helper's selected member
```
