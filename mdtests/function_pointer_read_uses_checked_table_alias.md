# A checked function-pointer read retains its table alias

```c filename=callback-read.c
struct callbacks { void (*call)(int *p); };
static void target(int *p) { }
static const struct callbacks table = { .call = target };
void copy(const struct callbacks *cb, struct callbacks *out) { out->call = cb->call; }
```

```click
verifying "callback-read.c";
void copy(const struct callbacks* cb, struct callbacks* out) {
    requires cb == &table;
    views cb->call;
    owns out->call;
    ensures out->call == (&table)->call;
} by {
    have separate(memory(out->call), memory(cb->call)) by assumption();
    mark write;
    transport((&table)->call == (&table)->call,
        cb->call == (&table)->call) using { cb == &table; };
    step();
    transport(at(write, cb->call) == at(write, (&table)->call),
        at(write, cb->call) == (&table)->call) using {
        at(write, cb->call) == at(write, (&table)->call);
        at(write, separate(memory(out->call), memory(cb->call)));
        cb == &table;
    };
    step();
    solve();
}
```

```expect
pass
```
