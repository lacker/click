# An inline callback refinement cannot establish another callback's contract

```c filename=inline_wrong.c
static inline int one(void) { return 1; }
static inline int two(void) { return 2; }
struct callbacks { int (*run)(void); };
static const struct callbacks table = { .run = two };
int invoke(const struct callbacks *p) { return p->run(); }
int caller(void) { return invoke(&table); }
```

```click
verifying "inline_wrong.c";
contract int32 One() { ensures result == 1; }
int32 one() { ensures result == 1; } by { execute(); normalize(); }
int32 two() { ensures result == 2; } by { execute(); normalize(); }
theorem one_contract() {
    ensures One(&one) by { unfold(One); simp(); }
}
resource callback_table(p: const struct callbacks*) {
    views p->run;
    fact One(p->run);
}
int32 invoke(const struct callbacks* p) {
    views callback_table(p);
    ensures result == 1;
} by { open(callback_table(p)) { execute(); simp(); } }
int32 caller() {
    views table.run;
    ensures result == 1;
} by {
    apply(one_contract());
    fold(callback_table(&table));
    execute(); simp();
}
```

```expect
fail: no `One(&two#inline:inline_wrong.c)` fact is available
```
