# A caller cannot reuse a named member consumed by a checked helper

```c filename=helper.c
void preserve(int32* pool) {}
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
void preserve(int32* pool) {
    owns authority(ticket(pool));
    consumes member: ticket(pool);
    ensures to_integer(count(ticket(pool))) == to_integer(old(count(ticket(pool))) - 1);
} by { unfold(member); }
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    let first = fold(ticket(&pool), { serial: 1 });
    step(preserve, { member: first });
    have first.serial == 1 by close();
    have to_integer(count(ticket(&pool))) == 1 by close();
    unfold(first);
    unfold(authority(ticket(&pool)));
}
```

```expect
fail: which is not held here
```
