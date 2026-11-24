# A helper with raw authority must spend a consumed member

The helper borrows `authority(ticket(p))` and declares `consumes ticket(p)`,
but its proof never unfolds the member. The standalone proof must check the
spend, so the helper is refused instead of letting its caller record a death.

```c filename=authority_helper_raw_consume_without_spend_rejected.c
void drop(void *p) {}
int run(void *p) { drop(p); return 1; }
```

```click
verifying "authority_helper_raw_consume_without_spend_rejected.c";
authorized resource ticket(p: void*) {}
void drop(void* p) {
    owns authority(ticket(p));
    consumes ticket(p);
}
int32 run(void* p) {
    owns authority(ticket(p));
    consumes ticket(p);
    requires count(ticket(p)) == 1;
    ensures result == 1;
} by {
    step();
    have count(ticket(p)) == 0;
    step(); close();
}
```

```expect
fail: Requires consumes ticket(p)
```
