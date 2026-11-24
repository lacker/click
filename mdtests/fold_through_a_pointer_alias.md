# A fold finds cells owned under another spelling of its address

An unfold publishes a child's cells under the pointer the parent's body
names, here the loaded `h->next`. A proof `match` arm names the same node by
its model binding `id`, and the child's arm states `p == id`. Refolding the
child at `id` requires those cells, so the fold must find them under the
spelling they were published at: the two pointers are proved equal, and a
proved equality puts their blocks in one pointer class.

Before, resource consumption looked only at the requested spelling, and the
fold was refused with "fold requires ownership of the complete instance
body". The Linux insert fixup's case-3 rotation needs this when a
great-grandparent frame's other child is unfolded to decide
`__rb_change_child` and refolded afterwards.

```c filename=fold_alias.c
struct node { unsigned long word; struct node *next; };

void keep(struct node *h) {
}
```

```click
verifying "fold_alias.c";

spec enum Cell { At(struct node*) }

resource cell_at(p: struct node*) {
    field model: Cell;
    match model {
        Cell::At(id) => {
            owns p->word;
            fact p != 0;
            fact p == id;
        },
    }
}

resource holder_at(h: struct node*) {
    field model: Cell;
    owns h->next;
    owns child: cell_at(h->next);
    fact child.model == model;
}

void keep(struct node* h) {
    owns g: holder_at(h);
} by {
    match g.model {
        Cell::At(id) => {
            let { child: c } = unfold(g);
            unfold(c);
            let c = fold(cell_at(id), { model: Cell::At(id) }) {
                requires id != 0 by close();
                requires id == id by normalize();
            }
            let g = fold(holder_at(h), { model: Cell::At(id), child: c });
            step_until(function.exit);
            close();
        },
    }
}
```

```expect
pass
```
