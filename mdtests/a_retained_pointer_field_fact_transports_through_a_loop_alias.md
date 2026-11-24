# A retained pointer-field fact transports through a loop alias

The companion of `a_retained_child_read_frames_across_a_call_through_a_loop_alias.md`
that carries a fact about the field rather than the field's read: the input
resource states `n->right == saved`, and the transport carries it across the
setter call that retains `n->right`. With the input opened and re-folded before
the loop, the fact is stated at the loop head. A small owned `saved_right`
resource retains it across the body's stores; unfolding that resource states
the preserved fact before the call. The explicit transport carries it on across
the call. The fact is a
pointer-value equality, and the transport once compared such facts only
exactly, refusing what the two-step form (transport the read, then rewrite)
proved.

```c filename=retained_field_fact.c
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
        n = p;
        break;
    }
}
```

```click
verifying "retained_field_fact.c";

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

                    have n->right == saved by {
                        have n->right == saved by {
                            close();
                        }
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
pass
```
