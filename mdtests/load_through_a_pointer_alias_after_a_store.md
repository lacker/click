# A read through one spelling sees a store through another

A resource arm names its cell by a model payload, `id->word`, and the C code
stores through a pointer it loaded, `p = c->up; p->word = 5;`. The arm's
fact `c->up == id` makes `p == id` provable. After the store, the value is
the same whichever spelling a proof reads it through, so `have id->word == 5`
holds exactly as `have p->word == 5` does.

The read through `id` stays a read at `id`: lowering does not respell it
through the pointer equality (lowering is fact-stable). The equality graph
equates a read with the value its state stores at an equal address under
another spelling, so the read meets the store through `p`.

```c filename=arm_identity_loaded.c
struct node { unsigned long word; struct node *up; };

void set_up_word(struct node *c) {
    struct node *p;
    p = c->up;
    p->word = 5;
}
```

```click
verifying "arm_identity_loaded.c";

spec enum Frame { Up(struct node*, int) }

resource frame_at(c: struct node*) {
    field model: Frame;
    match model {
        Frame::Up(id, value) => {
            owns c->up;
            owns id->word;
            fact id != 0;
            fact c->up == id;
            fact id->word == value;
        },
    }
}

void set_up_word(struct node* c) {
    consumes f: frame_at(c);
    produces g: frame_at(c);
} by {
    match f.model {
        Frame::Up(id, value) => {
            unfold(f);
            step();
            step();
            have separate(memory(p->word), memory(c->up));
            mark before_store;
            step();
            have separate(statement(2).footprint, memory(c->up)) by {
                normalize() using { separate(memory(p->word), memory(c->up)); };
            }
            have c->up == at(before_store, c->up) by {
                preserve(separate(statement(2).footprint, memory(c->up)));
            }
            have p == id;
            have p->word == 5;
            have id->word == 5;
            let g = fold(frame_at(c), { model: Frame::Up(id, 5) });
            step();
            solve();
        },
    }
}
```

```expect
pass
```
