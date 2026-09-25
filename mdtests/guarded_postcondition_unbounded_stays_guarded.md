# An unbounded guarded call postcondition stays guarded

`pick` promises `st.live == old(st.live) + result` only where that sum is
defined: the caller receives `defined(old(st.live) + got) implies st.live ==
old(st.live) + got`. Here nothing bounds `old(st.live)` or `got` from above,
so the sum can overflow and the guard cannot be discharged. `simp` must not
use the consequent, and `old(st.live) <= st.live` does not follow.

With bounds that exclude overflow the same closer does use it:
[`guarded_postcondition_closes_after_call.md`](guarded_postcondition_closes_after_call.md).

```c filename=guarded_postcondition_unbounded_stays_guarded.c
struct box {
    int v;
};

int pick(struct box* b) {
    return 0;
}

int caller(struct box* b) {
    int got;
    got = pick(b);
    return got;
}
```

```click
resource counted(b: struct box*) {
    field live: int32;
    owns object(b);
    fact 0 <= live;
}

verifying "guarded_postcondition_unbounded_stays_guarded.c";

int32 pick(struct box* b) {
    owns st: counted(b);
    ensures 0 <= result;
    ensures st.live == old(st.live) + result;
} by {
    let { live: n } = unfold(st);
    let st = fold(counted(b), { live: n });
    execute();
    simp();
}

int32 caller(struct box* b) {
    owns st: counted(b);
    ensures old(st.live) <= st.live;
} by {
    step();
    step(pick(b), { st: st });
    execute();
    simp();
}
```

```expect
fail: `ensures old(st.live) <= st.live` failed for `caller.ensures_1`
```
