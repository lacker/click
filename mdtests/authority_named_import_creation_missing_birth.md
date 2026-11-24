# Checked named births cross direct and nested helpers

```c filename=issue.c
void issue(int32* pool) {}
void nested(int32* pool) { issue(pool); }
int32 run() { int32 pool = 0; nested(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "issue.c";
void issue(int32* pool) {
    owns authority(ticket(pool));
    requires defined(count(ticket(pool)) + 1);
    produces member: ticket(pool);
    ensures member.serial == 7;
    ensures count(ticket(pool)) == old(count(ticket(pool))) + 1;
}
void nested(int32* pool) {
    owns authority(ticket(pool));
    requires defined(count(ticket(pool)) + 1);
    produces member: ticket(pool);
    ensures member.serial == 7;
    ensures count(ticket(pool)) == old(count(ticket(pool))) + 1;
} by { let { member: member } = step(issue); }
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    let retained = fold(ticket(&pool), { serial: 3 });
    let { member: member } = step(nested);
    have count(ticket(&pool)) == 2 by close();
    have member.serial == 7 by close();
    have retained.serial == 3 by close();
    unfold(member); unfold(retained); unfold(authority(ticket(&pool)));
}
```

```expect
fail: Requires
```
