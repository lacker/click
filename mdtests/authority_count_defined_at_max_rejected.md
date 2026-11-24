# A nonnegative population count can still be too large to increment

```c filename=count_defined.c
struct pool { int32 checked_out; };
void inspect(struct pool* pool) {}
```

```click
authorized resource item(pool: struct pool*, id: int32) {}
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(item(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(item(pool, _));
}
verifying "count_defined.c";
void inspect(struct pool* pool) {
    owns control(pool);
    requires pool->checked_out == 2147483647;
} by {
    with(control(pool)) {
        have count(item(pool, _)) == 2147483647 by close();
        have defined(count(item(pool, _)) + 1) by close();
    }
}
```

```expect
fail: could not establish `defined((count(item(pool, _)) + 1))`
```
