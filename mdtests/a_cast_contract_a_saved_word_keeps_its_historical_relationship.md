# A saved word keeps its relationship after its source is overwritten

```c filename=packed.c
struct node { int32 value; };
int32 read_packed(unsigned long* slot, struct node* p) {
    unsigned long saved = *slot;
    *slot = 0;
    return ((struct node*)(saved & ~1))->value;
}
```

```click
verifying "packed.c";
int32 read_packed(unsigned long* slot, struct node* p) {
    requires p != 0;
    requires ((*slot & ~1) as (struct node *)) == p;
    owns *slot;
    views p->value;
} by {
    mark before;
    step();
    have separate(statement(0).region(0).footprint, memory(*slot)) by {
        close() using {};
    }
    have *(slot as (int32 **)) == at(before, *(slot as (int32 **))) by {
        preserve(memory(*slot), statement(0).region(0));
    }
    have ((*slot & ~1) as (struct node *)) == p by {
        close();
    }
    step();
    have ((saved & ~1) as (struct node *)) == p by { close(); }
    step();
    have ((saved & ~1) as (struct node *)) == p by { close(); }
    step();
}
```

```expect
pass
```
