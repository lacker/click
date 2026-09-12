# An arm payload no premise pins names no cell

The negative for
[`guard_after_sibling_write_through_unfold.md`](guard_after_sibling_write_through_unfold.md).
There the requirement is `f.model == Frame::Held(x, 5)`, so the arm is selected
from a constructor and the projection knows `identity` is `x`. Here the only
requirement is `f.model != Frame::Top`, which selects the same arm on a
two-constructor model but says nothing about what it holds.

The arm's cell would then be `identity->next` for an unknown `identity`, which
is not the C parameter `x` and not any other name, so there is nothing for the
projection to name and nothing for the guard to decide. The refusal comes one
step earlier than that: `unfold` needs the constructor to bind the arm's
fields at all, so the disequality that selected the arm for *reading* is not
enough to open it. That is the ordinary consequence of a payload no premise
pins, not a gap, and it is why the projection only ever substitutes bindings a
constructor premise supplied.

```c filename=unknown_payload.c
struct link {
    struct link *next;
    int32 tag;
};

static inline void probe_ptr(struct link *x, struct link *y, struct link *z, int32 *out) {
    y->tag = 7;
    if (x->next == z)
        out[0] = 1;
    else
        out[0] = 2;
}

void run_frame(struct link *x, struct link *y, struct link *z, int32 *out) {
    probe_ptr(x, y, z, out);
}
```

```click
verifying "unknown_payload.c";

spec enum Frame {
    Top,
    Held(struct link*, int),
}

resource frame_at(child: struct link*) {
    field model: Frame;
    match model {
        Frame::Top => { fact child == 0; },
        Frame::Held(identity, v) => {
            owns identity->next;
            fact identity != 0;
            fact identity->next == child;
        },
    }
}

void run_frame(struct link* x, struct link* y, struct link* z, int32* out) {
    consumes f: frame_at(z);
    owns y->tag;
    owns out[0..1];
    requires f.model != Frame::Top;
    produces g: frame_at(z);
    ensures out[0] == 1;
} by {
    unfold(f);
    execute();
    let g = fold(frame_at(z), { model: old(f.model) }, {});
    simp();
}
```

```expect
fail: resource match requires constructor evidence for the instance field
```
