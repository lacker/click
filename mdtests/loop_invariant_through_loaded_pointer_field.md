# A contents invariant over a slice reached through a loaded pointer field

The written slice's base is `j->p`, a pointer loaded from a viewed field, not
a parameter. The quantified invariant's loadability leaves then need a
spelling for that base, and the smart certificate must name the owned range
through the same field read. This pins the synthesis that spells memory
reached through struct-pointer fields.

Initialization introduces the empty range and closes its contradictory guard.
Preservation proves the prefix through the element just written: earlier
indices use the invariant at the store's entry, while the final index uses
the store result. This explicit case split keeps the remaining smart closures
small enough to verify and expand under their ordinary budgets.

```c filename=probe_contract.c
struct job {
    int32 *p;
    int32 lo;
    int32 hi;
    int32 v;
};

int32 probe_contract(struct job *j) {
    int32 i;
    i = j->lo;
    while (i < j->hi) {
        j->p[i] = j->v;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "probe_contract.c";

resource task(j: struct job*) {
    views j->p;
    views j->lo;
    views j->hi;
    views j->v;
    owns j->p[j->lo..j->hi];
    fact 0 <= j->lo;
    fact j->lo <= j->hi;
    fact separate(memory(j[0..6]), memory(j->p[j->lo..j->hi]));
}

int32 probe_contract(struct job *j) {
    requires 0 <= j->lo;
    requires j->lo <= j->hi;
    requires separate(memory(j[0..6]), memory(j->p[j->lo..j->hi]));
    views j->p;
    views j->lo;
    views j->hi;
    views j->v;
    owns j->p[j->lo..j->hi];
    ensures result == j->hi;
    ensures forall (k: int32) { j->lo <= k and k < j->hi implies j->p[k] == j->v };
} by {
    step();
    step();
    loop as fill {
        invariant j->lo <= i and i <= j->hi;
        invariant forall (k: int32) { j->lo <= k and k < i implies j->p[k] == j->v };

        initialize by {
            have j->lo <= i and i <= j->hi by {
                both { normalize(); } and { assumption(); }
            }
            have forall (k: int32) { j->lo <= k and k < i implies j->p[k] == j->v } by {
                intro();
                intro();
                contradiction(j->lo <= k and k < i);
            }
        }
        preserve by {
            step();
            have forall (k: int32) { j->lo <= k and k <= i implies j->p[k] == j->v } by {
                intro();
                intro();
                if k < i {
                    extract(j->lo <= k);
                    instantiate(at(statement(3).entry, forall (k: int32) {
                        j->lo <= k and k < i implies j->p[k] == j->v
                    }), k) using { j->lo <= k; k < i; }
                    simp();
                } else {
                    extract(k <= i);
                    have k == i by {
                        apply(int32_le_and_not_lt_implies_eq(k, i)) using { k <= i; not (k < i); }
                    }
                    rewrite(k == i);
                    simp();
                }
            }
            step();
            simp();
        }
    }
    step();
    simp();
}
```

```termination
pending: unranked loop
```

```expect
pass
```
