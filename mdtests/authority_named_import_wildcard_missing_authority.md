# A named member cannot supply a missing helper authority

```c filename=helper.c
void preserve(int32* pool) {}
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*, tag: int32) { field serial: int32; }
resource control(pool: int32*) { owns authority(ticket(pool, _)); }
verifying "helper.c";
void preserve(int32* pool) {
    owns authority(ticket(pool, _));
    owns member: ticket(pool, 7);
    ensures member.serial == old(member.serial);
    ensures count(ticket(pool, _)) == old(count(ticket(pool, _)));
}
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool, _)));
    let first = fold(ticket(&pool, 7), { serial: 1 });
    fold(control(&pool));
    step(preserve, { member: first });
    have first.serial == 1 by close();
    have count(ticket(&pool, _)) == 1 by close();
    unfold(first);
    unfold(authority(ticket(&pool, _)));
}
```

```expect
fail: Requires owns authority(ticket(...))
```
