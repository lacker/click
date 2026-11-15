# A contents invariant over a slice reached through a loaded pointer field

The written slice's base is `j->p`, a pointer loaded from a viewed field, not
a parameter. The quantified invariant's viewability leaves then need a
spelling for that base, and the smart certificate must name the owned range
through the same field read. This pins the synthesis that spells memory
reached through struct-pointer fields.

Initialization introduces the empty range and closes its contradictory guard.
Preservation proves the prefix through the element just written: earlier
indices use the invariant at the store's entry, while the final index uses
the store result. This explicit case split keeps the remaining smart closures
small enough to verify and expand under their ordinary budgets.

The loop counts toward `j->hi`, a viewed field the body never writes, so the
measure reads it. The ranking members are named before the back edge in the
shape the obligation is built in. After the increment, the proof explicitly converts
`k < i` to `k <= at(region(4).entry, i)` and instantiates the filled-prefix
fact from that state. The final closer can then use the stated invariant
instead of rediscovering the quantified prefix extension through memory history.

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
    fact separate(memory(*j), memory(j->p[j->lo..j->hi]));
}

int32 probe_contract(struct job *j) {
    requires 0 <= j->lo;
    requires j->lo <= j->hi;
    requires separate(memory(*j), memory(j->p[j->lo..j->hi]));
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
        decreases j->hi - i;
        invariant j->lo <= i and i <= j->hi;
        invariant forall (k: int32) { j->lo <= k and k < i implies j->p[k] == j->v };

        initialize by {
            have j->lo <= i and i <= j->hi by {
                both { normalize(); } and { known(); }
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
                    instantiate(at(region(3).entry, forall (k: int32) {
                        j->lo <= k and k < i implies j->p[k] == j->v
                    }), k) using { j->lo <= k; k < i; };
                    solve();
                } else {
                    have k == i;
                    rewrite(k, i);
                    solve();
                }
            }
            step();
            have 0 <= at(region(3).entry, i) by {
                solve() using {
                    0 <= j->lo;
                    j->lo <= at(region(3).entry, i);
                };
            }
            have 0 <= j->hi by {
                solve() using {
                    0 <= j->lo;
                    j->lo <= j->hi;
                };
            }
            have 0 <= to_integer(0 - at(region(3).entry, i) + j->hi - 1) by {
                solve() using {
                    0 <= at(region(3).entry, i);
                    0 <= j->hi;
                    at(region(3).entry, i) < at(region(3).entry, j->hi);
                    j->lo <= j->hi;
                };
            }
            have to_integer(0 - at(region(3).entry, i) + j->hi - 1)
                < to_integer(0 - at(region(3).entry, i) + j->hi) by {
                solve() using {
                    0 <= at(region(3).entry, i);
                    0 <= j->hi;
                    at(region(3).entry, i) < at(region(3).entry, j->hi);
                    j->lo <= j->hi;
                };
            }
            have forall (k: int32) { j->lo <= k and k < i implies j->p[k] == j->v } by {
                intro();
                intro();
                have k <= at(region(4).entry, i) by {
                    solve() using {
                        k < i;
                        to_integer(i) == to_integer(at(region(4).entry, i) + 1);
                        at(region(4).entry, i) < j->hi;
                    };
                }
                instantiate(at(region(4).entry, forall (k: int32) {
                    j->lo <= k and k <= i implies j->p[k] == j->v
                }), k) using { j->lo <= k; k <= at(region(4).entry, i); };
                known();
            }
            solve();
        }
    }
    step();
    solve();
}
```

```expect
pass
```
