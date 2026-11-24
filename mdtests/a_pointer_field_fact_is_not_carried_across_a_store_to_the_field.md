# A pointer-field fact is not carried across a store to the field

The companion of `a_retained_pointer_field_fact_transports_through_a_loop_alias.md`
whose loop body also stores to `n->right` after the call. The fact is about an
older version of the cell, and the transport is refused.

```c filename=retained_field_fact_store.c
struct node {
    unsigned long word;
    struct node *right;
    struct node *left;
};

void set_word(struct node *m, struct node *p) {
    m->word = (unsigned long)p | 1;
}

void probe(struct node *g, struct node *n) {
    while (1) {
        struct node *p = g->left;
        struct node *tmp = n->left;
        p->right = tmp;
        n->left = p;
        set_word(tmp, p);
        n->right = 0;
        n = p;
        break;
    }
}
```

```click
verifying "retained_field_fact_store.c";

resource word_at(p: struct node*) {
    field tag: int32;
    owns p->word;
    fact tag == 0;
}

void set_word(struct node* m, struct node* p) {
    consumes w: word_at(m);
    produces after: word_at(m);
    ensures true;
} by {
    unfold(w);
    step_until(function.exit);
    let after = fold(word_at(m), { tag: 0 });
}

spec enum Anchor {
    At(struct node*, struct node*, struct node*, int32)
}

spec enum SavedPointer { At(struct node*) }

resource saved_right(n: struct node*) {
    field value: SavedPointer;
    match value {
        SavedPointer::At(saved) => {
            owns n->right;
            fact n->right == saved;
        },
    }
}

resource frame(g: struct node*, n: struct node*) {
    field anchor: Anchor;
    match anchor {
        Anchor::At(gg, nn, saved, tag) => {
            fact g == gg;
            fact n == nn;
            fact n->right == saved;
            owns g->left;
            owns g->left->right;
            owns n->left;
            owns n->right;
            owns word: word_at(n->left);
            fact word.tag == tag;
            fact g->left != 0;
            fact n->left != 0;
        },
    }
}

void probe(struct node* g, struct node* n) {
    consumes state: frame(g,n);
    ensures true;
} by {
    match state.anchor {
        Anchor::At(gg, nn, saved, tag) => {
            let { word: w } = unfold(state);
            let state = fold(frame(g,n), {
                anchor: old(state.anchor),
                word: w
            });

            loop {
                owns state: frame(g,n);
                invariant state.anchor == Anchor::At(gg, nn, saved, tag);
                invariant n == old(n);
                decreases 0;
                initialize by { close(); }
                maintain by {
                    let { word: w } = unfold(state);
                    let kept = fold(saved_right(n), { value: SavedPointer::At(saved) });
                    step(); step(); step(); step(); step(); step();
                    unfold(kept);

                    have n->right == saved;
                    mark before_call;
                    let { after: after } =
                        step(set_word, { w: w });
                    step();

                    have n->right == saved by {
                        close();
                    }

                    step(); step();
                }
            }

            step_until(function.exit); close();
        },
    }
}
```

```expect
fail: `solve` failed
```
