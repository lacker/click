# Rewriting an alias cannot restore an overwritten payload

The same alias rewrite must reject the old payload when the intervening
modular call writes the payload instead of preserving it.

```c filename=rewrite.c
struct child { int32 refs; int32 payload; };
struct holder { struct child* target; };
void put(struct holder* h, struct child* p) { h->target = p; }
void change(struct child* p) { p->payload = 0; }
int32 run(int32 value) {
    struct child* p = malloc(sizeof(struct child));
    if (p == 0) { return -1; }
    struct holder* h = malloc(sizeof(struct holder));
    if (h == 0) { free(p); return -1; }
    p->payload = value;
    put(h, p);
    change(p);
    free(h);
    free(p);
    return value;
}
```

```click
verifying "rewrite.c";
void put(struct holder* h, struct child* p) {
    owns &h->target;
    ensures h->target == p;
    ensures defined(h->target);
} by { execute(); simp(); }
void change(struct child* p) {
    owns object(p);
    ensures p->payload == 0;
} by { execute(); simp(); }
int32 run(int32 value) {
    ensures result == -1 or result == value;
} by {
    step(); step();
    branch { then { step(); simp(); } else {} }
    step(); step();
    branch { then { step(); step(); simp(); } else {} }
    step(); step(); step();
    have h->target->payload == value by { rewrite(h->target == p); simp(); }
    execute(); simp();
}
```

```expect
fail: `simp` failed for `run.contract`
```
