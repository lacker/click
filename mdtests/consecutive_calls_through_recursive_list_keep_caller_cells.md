# Consecutive calls through a recursive list keep a cell the caller owns

`caller` owns `flag[0..1]` beside a recursive `list_at(p)`, stores `5` in
`flag[0]`, lends the list to `overwrite` twice, and returns `flag[0]`.

Each call's footprint is every cell no other rule keeps, since the list is
recursive. The caller keeps owning `flag[0..1]` outside the transfer, so
the callee cannot write it: the first havoc drops the cell's cached value
and records the member that holds it on its edge, which names a load after
the call at the pre-call value. The second call found no cached cell to
record, so its edge kept nothing and the load after both calls was a fresh
value. A call whose footprint reaches unnamed memory now records every flat
member of what the caller keeps owning, cached or not.

```c filename=consecutive_calls_through_recursive_list_keep_caller_cells.c
struct cell {
    int32 value;
    struct cell* next;
};

void overwrite(struct cell* p) {
    p->value = 1;
}

int32 caller(struct cell* p, int32* flag) {
    flag[0] = 5;
    overwrite(p);
    overwrite(p);
    return flag[0];
}
```

```click
verifying "consecutive_calls_through_recursive_list_keep_caller_cells.c";

spec enum CellList {
    Nil,
    Cons(struct cell*, int32, CellList),
}

resource list_at(p: struct cell*) {
    field model: CellList;
    match model {
        CellList::Nil => { fact p == 0; },
        CellList::Cons(identity, value, tail_model) => {
            owns p->value;
            owns &p->next;
            owns tail: list_at(p->next);
            fact p != 0;
            fact p == identity;
            fact tail.model == tail_model;
        },
    }
}

void overwrite(struct cell* p) {
    owns l: list_at(p);
    requires l.model != CellList::Nil;
    ensures l.model != CellList::Nil;
} by {
    match l.model {
        CellList::Nil => { contradiction(l.model == CellList::Nil); },
        CellList::Cons(identity, value, tail_model) => {
            let { tail: t } = unfold(l);
            execute();
            let l = fold(list_at(p), {
                model: CellList::Cons(identity, 1, tail_model)
            }, { tail: t });
            simp();
        },
    }
}

int32 caller(struct cell* p, int32* flag) {
    owns l: list_at(p);
    owns flag[0..1];
    requires l.model != CellList::Nil;
    ensures result == 5;
} by {
    step();
    have flag[0] == 5 by simp;
    mark before;
    step(overwrite(p), { l: l });
    step(overwrite(p), { l: l });
    execute();
    simp();
}
```

```expect
pass
```
