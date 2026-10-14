# Another pool's control does not permit this quantity read

```c filename=quantity.c
struct pool { int32 capacity; };
void inspect(struct pool* pool, struct pool* other) {}
```

```click
authorized resource slot(pool: struct pool*) {}
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(slot(pool));
    fact pool->capacity == count(slot(pool));
}
verifying "quantity.c";
void inspect(struct pool* pool, struct pool* other) {
    owns control(other);
    requires pool != other;
    owns pool->capacity of slot(pool);
} by {
    execute(); simp();
}
```

```expect
fail: declared resource quantity could not be evaluated: required access authority is unavailable
```
