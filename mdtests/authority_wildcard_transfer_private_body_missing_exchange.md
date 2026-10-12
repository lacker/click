# Reject invalid cross-pool transfer: missing_exchange

```c filename=transfer_missing_exchange.c
void move(int32* source, int32* destination, int32* p) {}
```

```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "transfer_missing_exchange.c";
void move(int32* source, int32* destination, int32* p) {
    requires source != destination;
    owns authority(slot(source, _));
    owns authority(slot(destination, _));
    consumes slot(source, p);
    requires defined(count(slot(destination, _)) + 1);
    produces slot(destination, p);
    ensures p[0] == old(p[0]);
    ensures count(slot(source, _)) == old(count(slot(source, _))) - 1;
    ensures count(slot(destination, _)) == old(count(slot(destination, _))) + 1;
} by {
    execute(); simp();
}
```

```expect
fail: left `move.produces_0` unproved
```
