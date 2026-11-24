# A call's footprint includes memory a resource owns through a witness

`hop(p)` owns `*p` and, through an existential witness `next` that
`p->word` spells, the cell `next->value`. `holder(p, q)` contains `hop(p)`
and names a `side: tagged(q)` child. `overwrite` holds `holder(p, q)` and
stores `1` through the witness; its contract says nothing about the cell.
The caller stores `0` there, calls `overwrite`, and carries the `0` across
the call with `transport`, which would prove the false `result == 0`.

The footprint used to be enumerated by opening each held instance one body
layer, and `holder` names a child, so it could not be opened and
contributed nothing. The footprint is now derived from the definitions:
`holder`'s contained `hop(p)` is evaluated at the call, its witness bound as
`unfold` binds it, to the recorded origin of `p->word` (or else to a fresh
symbolic pointer, which no separation rule places apart from anything), so
the havoc covers `next->value` and the transport has no frame evidence.

```c filename=call_through_witness_footprint_includes_its_memory.c
struct node {
    int32 value;
    unsigned long word;
};

void overwrite(struct node* p, struct node* q) {
    struct node* next = (struct node*)(p->word & ~1);
    next->value = 1;
}

int32 caller(struct node* p, struct node* q) {
    struct node* next = (struct node*)(p->word & ~1);
    next->value = 0;
    overwrite(p, q);
    int32 seen = next->value;
    return seen;
}
```

```click
resource hop(node: struct node*) {
    owns *node;
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1) and ((node->word & ~1) as (struct node *)) == next;
    owns next->value;
}

resource tagged(q: struct node*) {
    field tag: int32;
    owns q->value;
}

resource holder(p: struct node*, q: struct node*) {
    field tag: int32;
    owns side: tagged(q);
    fact side.tag == tag;
    owns hop(p);
}

verifying "call_through_witness_footprint_includes_its_memory.c";

void overwrite(struct node* p, struct node* q) {
    requires p != 0;
    owns h: holder(p, q);
    ensures h.tag == old(h.tag);
} by {
    let { tag: t, side: s } = unfold(h);
    let { next: saved_next } = unfold(hop(p));
    mark before_word_0;
    step();
    have separate(statement(0).region(0).footprint, memory(p->word)) by {
        normalize() using { };
    }
    have p->word == at(before_word_0, p->word) by {
        preserve(memory(p->word), statement(0).region(0));
    }
    have *((&p->word) as (int32 **)) == at(before_word_0, *((&p->word) as (int32 **))) by {
        preserve(memory(p->word), statement(0).region(0));
    }
    mark before_word_1;
    step();
    have separate(statement(0).region(1).footprint, memory(p->word)) by {
        normalize() using { };
    }
    have p->word == at(before_word_1, p->word) by {
        preserve(memory(p->word), statement(0).region(1));
    }
    have *((&p->word) as (int32 **)) == at(before_word_1, *((&p->word) as (int32 **))) by {
        preserve(memory(p->word), statement(0).region(1));
    }
    mark before_word_2;
    have separate(memory((&next->value)[0..1]), memory(p->word));
    step();
    have separate(statement(1).footprint, memory(p->word)) by {
        normalize() using { separate(memory((&next->value)[0..1]), memory(p->word)); };
    }
    have p->word == at(before_word_2, p->word) by {
        preserve(memory(p->word), statement(1));
    }
    have *((&p->word) as (int32 **)) == at(before_word_2, *((&p->word) as (int32 **))) by {
        preserve(memory(p->word), statement(1));
    }

    have aligned(saved_next, 8) by close();
    have p->word == address(saved_next) + (p->word & 1) by {
        rewrite(p->word, at(before_word_0, p->word));
        close();
    }
    have ((p->word & ~1) as (struct node *)) == saved_next by {
        have ((p->word & ~1) as (struct node *)) == at(before_word_0, ((p->word & ~1) as (struct node *))) by {
            rewrite(p->word, at(before_word_0, p->word));
            close();
        }
        rewrite(((p->word & ~1) as (struct node *)), at(before_word_0, ((p->word & ~1) as (struct node *))));
        close();
    }
    fold(hop(p));
    let h = fold(holder(p, q), { tag: t, side: s });
}

int32 caller(struct node* p, struct node* q) {
    requires p != 0;
    owns h: holder(p, q);
    ensures result == 0;
} by {
    let { tag: t, side: s } = unfold(h);
    let { next: saved_next } = unfold(hop(p));
    mark before_word_0;
    step();
    have separate(statement(0).region(0).footprint, memory(p->word)) by {
        normalize() using { };
    }
    have p->word == at(before_word_0, p->word) by {
        preserve(memory(p->word), statement(0).region(0));
    }
    have *((&p->word) as (int32 **)) == at(before_word_0, *((&p->word) as (int32 **))) by {
        preserve(memory(p->word), statement(0).region(0));
    }
    mark before_word_1;
    step();
    have separate(statement(0).region(1).footprint, memory(p->word)) by {
        normalize() using { };
    }
    have p->word == at(before_word_1, p->word) by {
        preserve(memory(p->word), statement(0).region(1));
    }
    have *((&p->word) as (int32 **)) == at(before_word_1, *((&p->word) as (int32 **))) by {
        preserve(memory(p->word), statement(0).region(1));
    }
    mark before_word_2;
    have separate(memory((&next->value)[0..1]), memory(p->word));
    step();
    have separate(statement(1).footprint, memory(p->word)) by {
        normalize() using { separate(memory((&next->value)[0..1]), memory(p->word)); };
    }
    have p->word == at(before_word_2, p->word) by {
        preserve(memory(p->word), statement(1));
    }
    have *((&p->word) as (int32 **)) == at(before_word_2, *((&p->word) as (int32 **))) by {
        preserve(memory(p->word), statement(1));
    }

    have next->value == 0 by close();
    have aligned(saved_next, 8) by close();
    have p->word == address(saved_next) + (p->word & 1) by {
        rewrite(p->word, at(before_word_0, p->word));
        close();
    }
    have ((p->word & ~1) as (struct node *)) == saved_next by {
        have ((p->word & ~1) as (struct node *)) == at(before_word_0, ((p->word & ~1) as (struct node *))) by {
            rewrite(p->word, at(before_word_0, p->word));
            close();
        }
        rewrite(((p->word & ~1) as (struct node *)), at(before_word_0, ((p->word & ~1) as (struct node *))));
        close();
    }
    fold(hop(p));
    let h = fold(holder(p, q), { tag: t, side: s });
    mark before;
    step(overwrite, { h: h });
    let { tag: t2, side: s2 } = unfold(h);
    have next->value == at(before, next->value) by {
        close();
    }
    have next->value == 0 by close();
    let { next: saved_next } = unfold(hop(p));
    step();
    step();
    have aligned(saved_next, 8) by close();
    have p->word == address(saved_next) + (p->word & 1) by {
        rewrite(p->word, at(before_word_0, p->word));
        close();
    }
    have ((p->word & ~1) as (struct node *)) == saved_next by {
        have ((p->word & ~1) as (struct node *)) == at(before_word_0, ((p->word & ~1) as (struct node *))) by {
            rewrite(p->word, at(before_word_0, p->word));
            close();
        }
        rewrite(((p->word & ~1) as (struct node *)), at(before_word_0, ((p->word & ~1) as (struct node *))));
        close();
    }
    fold(hop(p));
    let h = fold(holder(p, q), { tag: t2, side: s2 });
}
```

```expect
fail: `solve` failed
```
