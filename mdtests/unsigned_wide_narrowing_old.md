# Casts inside old read entry memory, not the updated field

```c filename=old.c
struct state { unsigned long value; };
unsigned int take(struct state *p) {
    unsigned int result = p->value;
    p->value += 1;
    return result;
}
```

```click
verifying "old.c";
unsigned int take(struct state *p) {
    requires loadable(p->value);
    consumes p->value;
    produces p->value;
    ensures result == old((uint32)p->value);
    ensures p->value == old(p->value) + 1u64;
} by { execute(); simp(); }
```

```expect
pass
```
