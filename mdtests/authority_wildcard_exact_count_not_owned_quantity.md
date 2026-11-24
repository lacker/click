# One owned member does not establish a global exact count

```c filename=exact_count_not_owned.c
void inspect(int32* pool, int32* p) {}
```

```click
authorized resource slot(pool: int32*, p: int32*) {}
verifying "exact_count_not_owned.c";
void inspect(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    owns slot(pool, p);
} by {
    have count(slot(pool, p)) == 1 by close();
}
```

```expect
fail: could not establish `to_integer(count(slot(pool, p))) == 1`
```
