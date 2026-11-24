# A named child that holds a population member is refused

A named child beside the control's authority must not hide a population
member: a child whose definition owns a member reaches the population, so the
control cannot be folded or unfolded through the ordinary named exchange.


```c filename=authority_control_named_child_with_member_rejected.c
struct box { int32 used; int32 hits; };
int32 run() {
    struct box* b = malloc(sizeof(struct box));
    if (b == 0) return -1;
    b->used = 0;
    b->hits = 5;
    b->used = b->used + 1;
    b->used = b->used - 1;
    free(b);
    return 0;
}
```

```click
verifying "authority_control_named_child_with_member_rejected.c";

authorized resource ticket(b: struct box*) {}

resource hit_cell(b: struct box*) {
    field hits: int32;
    owns b->hits;
    owns ticket(b);
    fact b->hits == hits;
}

resource box_control(b: struct box*) {
    field hits: int32;
    owns b->used;
    owns stats: hit_cell(b);
    owns authority(ticket(b));
    fact stats.hits == hits;
    fact b->used == count(ticket(b));
}

int32 run() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch { true => { step(); close(); } false => {} }
    step();
    step();
    fold(authority(ticket(b)));
    fold(ticket(b));
    let s = fold(hit_cell(b), { hits: 5 });
    let ctl = fold(box_control(b), { hits: 5, stats: s });
    let { hits: hits, stats: s } = unfold(ctl);
    step();
    fold(ticket(b));
    let ctl = fold(box_control(b), { hits: hits, stats: s });
    let { hits: later_hits, stats: later } = unfold(ctl);
    unfold(ticket(b));
    step();
    unfold(later);
    have count(ticket(b)) == 0;
    unfold(authority(ticket(b)));
    step();
    step();
    close();
}
```

```expect
fail: named resource rewrite requires an ordinary memory body
```
