# A private-body member grants no population count observation

```c filename=wildcard_private_member_cannot_count.c
void inspect(int32* pool, int32* p) {}
```

```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_private_member_cannot_count.c";
void inspect(int32* pool, int32* p) {
    owns slot(pool, p);
} by {
    have count(slot(pool, p)) == 1 by close();
}
```

```expect
fail: count(...) requires owning authority for that population
```
