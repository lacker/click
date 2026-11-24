# An equal loaded pointer does not justify a false field fact

Reading `r->tag` through the loaded pointer equal to `q` reaches `q->tag`,
whose low bit is 1; a claim that it is 0 is not an available fact.

```c filename=pointer_field_alias.c
struct Node { unsigned long tag; struct Node *next; };
void check(struct Node *p, struct Node *q) {
    struct Node *r = p->next;
}
```

```click
verifying "pointer_field_alias.c";
void check(struct Node* p, struct Node* q) {
    owns p->next;
    owns q->tag;
    requires p->next == q;
    requires (q->tag & 1) == 1;
} by {
    step(); step();
    have r == q;
    have (r->tag & 1) == 0 by close();
}
```

```expect
fail: could not establish `(r->tag & 1) == 0`
```
