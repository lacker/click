# A preserved child value grants no read after ownership is consumed

The child value is preserved across the disjoint store to `root->value`.
The proof also separates the child's value from the borrowed pointer cell
before refolding and transferring the resource to `consume_child`.
Knowing its value before that call does not supply ownership for the final read.

```c filename=guarded.c
struct base { struct base* left; struct base* right; uint64 padding; };
struct cell { struct base base; int32 value; };
void consume_child(struct base *p);
int32 f(struct cell* root) {
    struct base* child = root->base.left;
    int32 value = ((struct cell*)(void*)child)->value;
    root->value = value;
    consume_child(child);
    return ((struct cell*)(void*)child)->value;
}
```

```click
verifying "guarded.c";
resource child_value(p: struct base*) {
    field number: int32;
    if p != 0 {
        owns (p as (void *) as (struct cell *))->value;
        fact (p as (void *) as (struct cell *))->value == number;
    }
}
extern void consume_child(struct base *p) {
    consumes state: child_value(p);
}
int32 f(struct cell* root) {
    requires root != 0;
    views root->base.left;
    consumes child: child_value(root->base.left);
    owns root->value;
    requires root->base.left != 0;
    requires root->base.left != root as (void *) as (struct base *);
    ensures result == old(child.number);
    ensures root->value == old(child.number);
} by {
    unfold(child);
    have separate(memory((root->base.left as (void *) as (struct cell *))->value), memory(root->value));
    step(); step(); step(); step();
    mark before_store;
    step();
    have contains(memory(root->value), memory((&root->value)[0..1])) by { normalize(); }
    have contains(memory((root->base.left as (void *) as (struct cell *))->value), memory((&((root->base.left as (void *) as (struct cell *))->value))[0..1])) by { normalize(); }
    have separate(memory((&((root->base.left as (void *) as (struct cell *))->value))[0..1]), memory((&root->value)[0..1])) by {
        apply(click::separation::separate_restrict(
            memory((root->base.left as (void *) as (struct cell *))->value), memory(root->value),
            memory((&((root->base.left as (void *) as (struct cell *))->value))[0..1]), memory((&root->value)[0..1])));
    }
    have separate(statement(2).footprint, memory((&((root->base.left as (void *) as (struct cell *))->value))[0..1])) by {
        close();
    }
    have (root->base.left as (void *) as (struct cell *))->value == at(before_store, (root->base.left as (void *) as (struct cell *))->value) by {
        preserve(memory((&((root->base.left as (void *) as (struct cell *))->value))[0..1]), statement(2));
    }
    have separate(memory((root->base.left as (void *) as (struct cell *))->value), memory(root->base.left)) by { close(); }
    let restored = fold(child_value(root->base.left), { number: old(child.number) });
    step() by { close(); }
    step(); close();
}
```

```expect
fail: missing resource fact
```
