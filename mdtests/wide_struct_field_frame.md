# A wide field update preserves the neighboring wide field

```c filename=frame.c
struct pair { unsigned long a; unsigned long b; };
unsigned long update(struct pair *p) { p->a += 1; return p->b; }
```

```click
verifying "frame.c";
unsigned long update(struct pair *p) {
    requires loadable(p->a);
    requires loadable(p->b);
    consumes p->a;
    consumes p->b;
    produces p->a;
    produces p->b;
    ensures result == old(p->b);
    ensures p->a == old(p->a) + 1u64;
} by { execute(); simp(); }
```

```expect
pass
```
