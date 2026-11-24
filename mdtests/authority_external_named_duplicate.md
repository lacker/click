# One named occurrence cannot fill two authority-helper binders

```c filename=helper.c
extern void preserve(int32* pool);
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
extern void preserve(int32* pool) {
    owns authority(ticket(pool));
    owns left: ticket(pool);
    owns right: ticket(pool);
    ensures left.serial == old(left.serial);
    ensures right.serial == old(right.serial);
    ensures count(ticket(pool)) == old(count(ticket(pool)));
}
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    let first = fold(ticket(&pool), { serial: 1 });
    let second = fold(ticket(&pool), { serial: 2 });
    step(preserve, { left: first, right: first });
    have first.serial == 1 by close();
    have second.serial == 2 by close();
    have count(ticket(&pool)) == 2 by close();
    unfold(first); unfold(second);
    unfold(authority(ticket(&pool)));
}
```

```expect
fail: cannot supply two binders
```
