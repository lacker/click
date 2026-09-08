# Read an existing unsigned 64-bit struct field

```c filename=read.c
struct state { unsigned long value; };
static struct state global = { 0x853c49e6748fea9bULL };
unsigned long read_state(struct state *p) { unsigned long v = p->value; return v; }
```

```click
verifying "read.c";
unsigned long read_state(struct state *p) {
    requires loadable(p->value);
    consumes p->value;
    produces p->value;
    ensures result == old(p->value);
} by { execute(); simp(); }
```

```expect
pass
```
