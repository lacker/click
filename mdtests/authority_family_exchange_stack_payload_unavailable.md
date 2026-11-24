# Resource counts alone do not preserve a local record payload

Automatic records have transferable storage ownership. This helper exports
resource counts but no payload-value guarantee, so reading the returned body
does not recover the caller's old value or prove the addition cannot overflow.

```c filename=family_exchange.c
struct payload { int32 value; };
void checkout(int32* pool, struct payload* p) {}
int32 lifecycle() {
    int32 pool = 0;
    struct payload first;
    struct payload second;
    first.value = 1;
    second.value = 2;
    checkout(&pool, &first);
    int32 result = first.value + second.value;
    return result;
}
```

```click
authorized resource capacity(pool: int32*) {}
authorized resource item(pool: int32*, p: struct payload*) { owns *p; }
verifying "family_exchange.c";
void checkout(int32* pool, struct payload* p) {
    owns authority(capacity(pool));
    owns authority(item(pool, _));
    consumes capacity(pool);
    consumes *p;
    requires defined(count(item(pool, _)) + 1);
    requires count(item(pool, p)) == 0;
    produces item(pool, p);
    ensures count(capacity(pool)) == old(count(capacity(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
    ensures count(item(pool, p)) == 1;
} by {
    unfold(capacity(pool));
    fold(item(pool, p));
}
int32 lifecycle() { ensures result == 3; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(capacity(&pool)));
    fold(authority(item(&pool, _)));
    fold(capacity(&pool));
    fold(capacity(&pool));
    fold(item(&pool, &second));
    step();
    have count(capacity(&pool)) == 1 by close();
    have count(item(&pool, _)) == 2 by close();
    have count(item(&pool, &first)) == 1 by close();
    have count(item(&pool, &second)) == 1 by close();
    with(item(&pool, &first)) { with(item(&pool, &second)) { step(); step(); } }
    unfold(capacity(&pool));
    unfold(item(&pool, &first));
    unfold(item(&pool, &second));
    unfold(authority(capacity(&pool)));
    unfold(authority(item(&pool, _)));
}
```

```expect
fail: signed overflow
```
