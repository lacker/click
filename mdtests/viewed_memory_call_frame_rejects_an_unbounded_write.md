# A recursive write bound must be separate from the whole live-view frame

Separation from just one of the two live views is insufficient. The call's
prerequisite names the recursive input resource and the complete view footprint.

```c filename=unbounded_write.c
struct node { struct node *next; };
void touch(struct node *p) {}
void caller(struct node *p, int *viewed, int *other) { touch(p); }
```

```click
import click::separation;
verifying "unbounded_write.c";

resource list(p: struct node*) {
    if p != 0 {
        owns p->next;
        owns list(p->next);
    }
}

void touch(struct node* p) { owns list(p); }
void caller(struct node* p, int* viewed, int* other) {
    requires p != 0;
    owns list(p);
    views viewed[0..1];
    views other[0..1];
    requires separate(list(p), memory(viewed[0]));
} by {
    step() {
        requires separate(list(p), memory(viewed[0])) by close();
    }
}
```

```expect
fail: it does not require it; it leaves open `separate(list(p), (memory((viewed as (int32 *))[0..1]) * memory((other as (int32 *))[0..1])))`
```
