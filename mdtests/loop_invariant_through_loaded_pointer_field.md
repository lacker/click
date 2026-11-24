# A contents invariant over a slice reached through a loaded pointer field

The written slice's base is `j->p`, a pointer loaded from a viewed field, not
a parameter. The quantified invariant's viewability leaves then need a
spelling for that base, and the smart certificate must name the owned range
through the same field read. This pins the synthesis that spells memory
reached through struct-pointer fields.

Initialization proves the prefix is empty. Before the store, containment
narrows the contract's separation of the slice and the struct to the element
being written. After the store, the same separation preserves the struct
fields. Every earlier index is distinct from the written index, so its value
comes from the saved invariant. The final index gets its value from the store.

The rank is the distance from `i` to `j->hi` in mathematical integers.
The increment reduces that distance by one and turns the inclusive prefix
after the store into the strict prefix required at the next loop head.

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
import click::integer;
import click::separation;
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
    loop fill {
        decreases to_integer(j->hi) - to_integer(i);
        invariant j->lo <= i and i <= j->hi;
        invariant forall (k: int32) { j->lo <= k and k < i implies j->p[k] == j->v };

        initialize by {
            have j->lo <= i and i <= j->hi by {
                all { j->lo <= i => { normalize(); } i <= j->hi => { close(); } }
            }
            have forall (k: int32) { j->lo <= k and k < i implies j->p[k] == j->v } by {
                intro();
                intro();
                contradiction(j->lo <= k and k < i);
            }
        }
        maintain by {
            mark before_write;
            have separate(memory(*j), memory(j->p[j->lo..j->hi])) by { close(); }
            have contains(memory(j->p[j->lo..j->hi]), memory(j->p[i])) by {
                apply(separation::contains_element(j->p, j->lo, j->hi, i));
            }
            apply(separation::contains_refl(memory(*j)));
            apply(separation::separate_restrict(memory(*j), memory(j->p[j->lo..j->hi]),
                memory(*j), memory(j->p[i])));
            step() by { close(); }

            have separate(statement(2).statement(0).footprint, at(before_write, memory(*j))) by {
                normalize() using {
                    separate(at(before_write, memory(j->p[i])), at(before_write, memory(*j)));
                };
            }
            apply(separation::contains_refl(statement(2).statement(0).footprint));
            have contains(at(before_write, memory(*j)), at(before_write, memory(j->lo))) by { normalize(); }
            apply(separation::separate_restrict(statement(2).statement(0).footprint, at(before_write, memory(*j)),
                statement(2).statement(0).footprint, at(before_write, memory(j->lo))));
            have j->lo == at(before_write, j->lo) by {
                preserve(at(before_write, memory(j->lo)), statement(2).statement(0));
            }
            have contains(at(before_write, memory(*j)), at(before_write, memory(j->p))) by { normalize(); }
            apply(separation::separate_restrict(statement(2).statement(0).footprint, at(before_write, memory(*j)),
                statement(2).statement(0).footprint, at(before_write, memory(j->p))));
            have j->p == at(before_write, j->p) by {
                preserve(at(before_write, memory(j->p)), statement(2).statement(0));
            }
            have contains(at(before_write, memory(*j)), at(before_write, memory(j->hi))) by { normalize(); }
            apply(separation::separate_restrict(statement(2).statement(0).footprint, at(before_write, memory(*j)),
                statement(2).statement(0).footprint, at(before_write, memory(j->hi))));
            have j->hi == at(before_write, j->hi) by {
                preserve(at(before_write, memory(j->hi)), statement(2).statement(0));
            }
            have contains(at(before_write, memory(*j)), memory(at(before_write, &j->v)[0])) by { normalize(); }
            apply(separation::separate_restrict(statement(2).statement(0).footprint, at(before_write, memory(*j)),
                statement(2).statement(0).footprint, memory(at(before_write, &j->v)[0])));
            have load<int32>(at(before_write, &j->v)) == at(before_write, load<int32>(&j->v)) by {
                preserve(memory(at(before_write, &j->v)[0]), statement(2).statement(0));
            }
            have j->v == at(before_write, j->v) by { close(); }

            have forall (k: int32) { j->lo <= k and k <= i implies j->p[k] == j->v } by {
                intro();
                intro();
                if k < i {
                    instantiate(at(region(3).entry, forall (k: int32) {
                        j->lo <= k and k < i implies j->p[k] == j->v
                    }), k);
                    have at(region(3).entry, j->lo) <= k and k < at(before_write, i) by {
                        rewrite(at(region(3).entry, j->lo), j->lo);
                        close();
                    }
                    apply(at(region(3).entry, j->lo) <= k and k < at(before_write, i) implies
                        at(before_write, j->p[k]) == at(before_write, j->v));
                    have k != at(before_write, i) by { close() using { k < i; }; }
                    have separate(at(before_write, memory(j->p[k])), at(before_write, memory(j->p[i]))) by {
                        apply(separation::separate_elements(at(before_write, j->p), k, at(before_write, i)));
                    }
                    have separate(statement(2).statement(0).footprint, at(before_write, memory(j->p[k]))) by {
                        normalize() using {
                            separate(at(before_write, memory(j->p[k])), at(before_write, memory(j->p[i])));
                        };
                    }
                    have load<int32>(at(before_write, &j->p[k])) == at(before_write, j->p[k]) by {
                        preserve(at(before_write, memory(j->p[k])), statement(2).statement(0));
                    }
                    rewrite(j->p, at(before_write, j->p));
                    rewrite(j->v, at(before_write, j->v));
                    close();
                } else {
                    have k == i;
                    rewrite(k, i);
                    close();
                }
            }

            step();
            have at(before_write, i) < j->hi by {
                rewrite(j->hi, at(before_write, j->hi));
                close();
            }
            have at(region(4).entry, i) < 2147483647 by {
                apply(integer::int32_less_than_less_equal_transitive(at(region(4).entry, i), j->hi, 2147483647));
            }
            apply(integer::int32_increment_below_max_is_defined(at(region(4).entry, i)));
            have to_integer(i) == to_integer(at(before_write, i)) + 1 by {
                have to_integer(i) == to_integer(at(region(4).entry, i) + 1) by { close(); }
                apply(integer::int32_add_to_integer(at(region(4).entry, i), 1));
                close();
            }
            have forall (k: int32) { j->lo <= k and k < i implies j->p[k] == j->v } by {
                intro();
                intro();
                have k <= at(region(4).entry, i) by {
                    have to_integer(k) < to_integer(i) by { close(); }
                    apply(integer::lt_le_predecessor(to_integer(k), to_integer(i)));
                    have to_integer(at(region(4).entry, i)) == to_integer(i) - 1 by {
                        rewrite(to_integer(i), to_integer(at(before_write, i)) + 1);
                        close();
                    }
                    have to_integer(k) <= to_integer(at(region(4).entry, i)) by {
                        rewrite(to_integer(at(region(4).entry, i)), to_integer(i) - 1);
                        close();
                    }
                    apply(integer::int32_to_integer_less_equal_implies_less_equal(k, at(region(4).entry, i)));
                }
                instantiate(at(region(4).entry, forall (k: int32) {
                    j->lo <= k and k <= i implies j->p[k] == j->v
                }), k);
                have at(region(4).entry, j->lo) <= k and k <= at(region(4).entry, i) by { close(); }
                apply(at(region(4).entry, j->lo) <= k and k <= at(region(4).entry, i) implies
                    at(region(4).entry, j->p[k]) == at(region(4).entry, j->v));
                close();
            }
            have j->lo <= i by {
                have at(region(4).entry, j->lo) <= at(region(4).entry, i) by { close(); }
                apply(integer::int32_increment_lower_bound(at(region(4).entry, i), at(region(4).entry, j->lo), j->hi));
                have to_integer(j->lo) <= to_integer(i) by { close(); }
                apply(integer::int32_to_integer_less_equal_implies_less_equal(j->lo, i));
            }
            have i <= j->hi by {
                apply(integer::int32_increment_upper_bound(at(region(4).entry, i), j->hi));
                have to_integer(i) <= to_integer(j->hi) by { close(); }
                apply(integer::int32_to_integer_less_equal_implies_less_equal(i, j->hi));
            }
            have 0 <= to_integer(j->hi) - to_integer(i) by {
                close() using { i <= j->hi; };
            }
            have to_integer(j->hi) - to_integer(i) < at(before_write, to_integer(j->hi) - to_integer(i)) by {
                rewrite(to_integer(i), to_integer(at(before_write, i)) + 1);
                rewrite(at(before_write, j->hi), j->hi);
                close();
            }
            close();
        }
    }
    have i == j->hi by {
        have i <= j->hi by { close(); }
        have not (i < j->hi) by { close(); }
        apply(integer::int32_less_equal_and_not_less_than_implies_equal(i, j->hi));
    }
    have forall (k: int32) { j->lo <= k and k < j->hi implies j->p[k] == j->v } by {
        intro();
        intro();
        instantiate(forall (k: int32) { j->lo <= k and k < i implies j->p[k] == j->v }, k);
        have j->lo <= k and k < i by {
            rewrite(i, j->hi);
            close();
        }
        apply(j->lo <= k and k < i implies j->p[k] == j->v);
        close();
    }
    step();
    close();
}
```

```expect
pass
```
