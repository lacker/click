# A saved field address uses the saved enclosing pointer

Changing a link must not retarget the address saved through that link.

```c filename=saved_field.c
struct box { int value; };
struct link { struct box *ptr; };
void redirect(struct link *r, struct box *q) { r->ptr = q; }
```

```click
verifying "saved_field.c";
void redirect(struct link *r, struct box *q) {
    owns *r;
    views r->ptr->value;
    views *q;
    requires separate(memory(r->ptr->value), memory(q->value));
} by {
    mark before;
    have separate(memory(at(before, &r->ptr->value)[0]), memory((&q->value)[0..1])) by { known(); }
    step();
    have separate(memory(at(before, &r->ptr->value)[0]), memory((&q->value)[0..1])) by { known(); }
    step();
}
```

```expect
pass
```
