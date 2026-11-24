# Callback ownership does not establish a different target's contract

```c filename=callbacks.c
struct callbacks { void (*call)(int *p); };
static void target(int *p) { }
static void other(int *p) { }
static const struct callbacks table = { .call = other };
void concrete(int *p) {
 const struct callbacks *cb = &table;
 cb->call(p);
}
void symbolic(int *p, const struct callbacks *cb) { cb->call(p); }
```

```click
verifying "callbacks.c";
contract void Invoke(int32* p) { ensures true; }
void target(int32* p) { ensures true; } by { step_until(function.exit); close(); }
theorem target_has_contract()
executes target(int32* p) {
    ensures Invoke(&target) by { step_until(function.exit); close(); }
}
void symbolic(int32* p, const struct callbacks* cb) {
    requires cb == &table;
    views cb->call;
    ensures true;
} by {
    have cb == &table by { close(); }
    apply(target_has_contract());
    step(Invoke);
    step_until(function.exit); close();
}
```

```expect
fail: contract `Invoke` is not established for this callback with its call signature
```
