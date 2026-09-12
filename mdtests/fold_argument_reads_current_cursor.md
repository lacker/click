# a proof `fold` reads its resource arguments at the cursor it stands on

A contract clause speaks about parameters, so `holds(q)` in a `consumes` clause
is the instance at the entry argument. A `fold` inside a proof is not a
contract clause: it names the state the execution has reached. After `p = q`
the cell the proof owns is `holds(p)`, because `p` is now the cursor the body
walked to.

Reading a fold's arguments at entry instead split one tactic across two
states. The fold's field values already come from the current locals
(`contract_environment_at_state`), so the instance was built at the entry
address while its fields described the current one, and the fold was refused
for want of ownership of a body it had never been handed.

```c filename=fold_argument_reads_current_cursor.c
struct cell { int32 value; };

struct cell *adopt(struct cell *p, struct cell *q) {
    p = q;
    return p;
}
```

```click
verifying "fold_argument_reads_current_cursor.c";

spec enum Maybe { None, Some(int32) }

resource holds(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

struct cell* adopt(struct cell* p, struct cell* q) {
    consumes a: holds(q);
    requires a.model != Maybe::None;
    produces b: holds(result);
    ensures b.model == old(a.model);
} by {
    match a.model {
        Maybe::None => { contradiction(a.model == Maybe::None); },
        Maybe::Some(value) => {
            unfold(a);
            step();
            let b = fold(holds(p), { model: Maybe::Some(value) });
            step();
            simp();
        },
    }
}
```

```expect
pass
```
