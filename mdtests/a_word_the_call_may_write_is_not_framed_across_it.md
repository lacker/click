# A word the call may write is not framed across it

The negative companion of
`a_retained_word_frames_across_a_call_through_a_loop_alias.md`: the call now
consumes the resource that owns `n->word` and writes it, so the word before the
call says nothing about the word after it, and the same transport is refused.

```c filename=overwritten_word.c
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
        set_word(n, p);
        n = p;
        break;
    }
}
```

```click
verifying "overwritten_word.c";

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
            owns nw: word_at(n);
            fact nw.tag == tag;
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
            let { word: w, nw: v } = unfold(state);
            let state = fold(frame(g,n), {
                anchor: old(state.anchor),
                word: w, nw: v
            });

            loop {
                owns state: frame(g,n);
                invariant state.anchor == Anchor::At(gg, nn, saved, tag);
                invariant n == old(n);
                decreases 0;
                initialize by { close(); }
                maintain by {
                    let { word: w, nw: v } = unfold(state);
                    step(); step(); step(); step(); step(); step();

                    mark before_call;
                    let { after: after } =
                        step(set_word, { w: v });

                    have n->word == at(before_call, n->word) by {
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
