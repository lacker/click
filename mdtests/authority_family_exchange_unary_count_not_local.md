# Unary authority does not equate the global total to local custody

```c filename=unary_count_not_local.c
void inspect(int32* pool) {}
```

```click
authorized resource capacity(pool: int32*) {}
verifying "unary_count_not_local.c";
void inspect(int32* pool) {
    owns authority(capacity(pool));
    owns capacity(pool);
} by {
    have count(capacity(pool)) == 1 by close();
}
```

```expect
fail: could not establish `to_integer(count(capacity(pool))) == 1`
```
