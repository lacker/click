# A static inline callback has the same identity in C and its contract fact

```c filename=inline_callback.c
static inline void quiet(void) { }
struct callbacks { void (*run)(void); };
static const struct callbacks table = { .run = quiet };
void invoke(const struct callbacks *p) { p->run(); }
void caller(void) { invoke(&table); }
```

```click
verifying "inline_callback.c";
contract void Quiet() { ensures 1 == 1; }
void quiet() { ensures 1 == 1; } by { execute(); normalize(); }
theorem quiet_contract() {
    ensures Quiet(&quiet) by { unfold(Quiet); simp(); }
}
theorem quiet_by_execution() executes quiet() {
    ensures Quiet(&quiet) by { execute(); normalize(); }
}
resource callback_table(p: const struct callbacks*) {
    views p->run;
    fact Quiet(p->run);
}
void invoke(const struct callbacks* p) {
    views callback_table(p);
    ensures 1 == 1;
} by { open(callback_table(p)) { execute(); normalize(); } }
void caller() {
    views table.run;
    ensures 1 == 1;
} by {
    apply(quiet_contract());
    fold(callback_table(&table));
    execute(); normalize();
}
```

```expect
pass
```
