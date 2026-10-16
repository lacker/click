# Archived iterated give loses descriptor ownership across a loop

Priority: P2.

Soundness: not soundness. The recovery object-model implementation refuses a
valid ownership transfer. This reproduction does not demonstrate false
acceptance.

## Reproduction

At recovery checkpoint `b5e26dcf6`, save the following as `probe.c` and
`probe.click`, then run `click verify probe.click`. It stops at
`release_run.contract` tactic 14: `give(arena->data[i..i + 1])` reports that the
element is not owned. The complete proof passes upstream baseline `64f0f0d46`
with `import click::machine_integer;` prepended for that revision's modular
standard library. The Rust verifier sources at `95fe8cbd1` and `64f0f0d46` are
identical; the baseline helper was linked from that implementation.

This reduces the original `arena_free` failure while preserving the descriptor
field accesses, loop, occupancy store and increment. The descriptor itself is
viewed, not written. The window owns the suffix `data[next..end]`, `next == i`,
and the loop establishes `i < end`. Storing zero makes the iterated guard true,
so returning that owned element is valid.

```c filename=probe.c
struct arena { int32* data; int32* occupied; int32 capacity; };
void release_run(struct arena* arena, int32 start, int32 end) {
    int32 i;
    i = start;
    while (i < end) {
        arena->occupied[i] = 0;
        i = i + 1;
    }
}
```

```click filename=probe.click
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

resource arena_clear_window(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    start: int32,
    end: int32
) {
    field next: int32;
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
    owns data[next..end];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact separate(memory(occupied[0..capacity]), memory(data[0..capacity]));
    fact forall (k: int32) {
        start <= k and k < next implies occupied[k] == 0
    };
}


verifying "probe.c";
void release_run(struct arena* arena, int32 start, int32 end) {
    views arena->data; views arena->occupied; views arena->capacity;
    consumes w: arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end);
    requires w.next == start;
    requires arena->capacity <= 536870911;
    produces arena_cells(arena->data, arena->occupied, arena->capacity);
} by {
    step(); step();
    loop as clear_occupied {
        decreases end - i;
        owns w: arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end);
        invariant w.next == i;
        invariant forall (k: int32) {
            0 <= k and k < start implies
                arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
        };
        invariant forall (k: int32) {
            end <= k and k < arena->capacity implies
                arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
        };
        initialize by simp;
        preserve by {
            let { next: m } = unfold(w);
            have m == i;
            have 0 <= start;
            have start <= m;
            have start <= i;
            have 0 <= i by {
                apply(int32_less_equal_transitive(0, start, i)) using {
                    0 <= start;
                    start <= i;
                }
            }
            have end <= arena->capacity;
            have i < arena->capacity by auto;
            mark opened;
            step();
            give(arena->data[i..i + 1]);
            step();
            have start <= at(opened, i) + 1 by {
                apply(int32_increment_lower_bound(at(opened, i), start, end)) using {
                    start <= at(opened, i);
                    at(opened, i) < end;
                }
            }
            have forall (k: int32) {
                start <= k and k < at(opened, i) + 1 implies arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(start <= k);
                extract(k < at(opened, i) + 1);
                if k < at(opened, i) {
                    have k < m;
                    have at(opened, arena->occupied[k]) == 0 by {
                        instantiate(forall (j: int32) {
                            at(opened, start) <= at(opened, j) and
                                at(opened, j) < at(opened, m) implies
                                at(opened, arena->occupied[j]) == at(opened, 0)
                        }, k) using {
                            start <= k;
                            k < m;
                        }
                        assumption();
                    }
                    have 0 <= k by {
                        apply(int32_less_equal_transitive(0, start, k)) using {
                            0 <= start;
                            start <= k;
                        }
                    }
                    transport(at(opened, arena->occupied[k]) == 0, arena->occupied[k] == 0) using {
                        at(opened, arena->occupied[k]) == 0;
                        k < at(opened, i);
                        0 <= k;
                        0 <= at(opened, i);
                        at(opened, i) < arena->capacity;
                    }
                } else {
                    have k <= at(opened, i) by {
                        apply(int32_less_than_increment_implies_less_equal(k, at(opened, i))) using {
                            k < at(opened, i) + 1;
                        }
                    }
                    have k == at(opened, i) by {
                        apply(int32_less_equal_and_not_less_than_implies_equal(k, at(opened, i))) using {
                            k <= at(opened, i);
                            not (k < at(opened, i));
                        }
                    }
                    rewrite(k == at(opened, i));
                    normalize();
                }
            }
            have forall (k: int32) {
                0 <= k and k < start implies
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < start);
                have at(opened, arena->occupied[k]) ==
                    at(clear_occupied.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        at(opened, 0) <= at(opened, j) and
                            at(opened, j) < at(opened, start) implies
                            at(opened, arena->occupied[j]) ==
                                at(clear_occupied.entry, arena->occupied[j])
                    }, k) using {
                        0 <= k;
                        k < start;
                    }
                    assumption();
                }
                have k < at(opened, i) by auto;
                transport(
                    at(opened, arena->occupied[k]) ==
                        at(clear_occupied.entry, arena->occupied[k]),
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
                ) using {
                    at(opened, arena->occupied[k]) ==
                        at(clear_occupied.entry, arena->occupied[k]);
                    k < at(opened, i);
                    0 <= k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
                }
            }
            have forall (k: int32) {
                end <= k and k < arena->capacity implies
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
            } by {
                intro();
                intro();
                extract(end <= k);
                extract(k < arena->capacity);
                have at(opened, arena->occupied[k]) ==
                    at(clear_occupied.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        at(opened, end) <= at(opened, j) and
                            at(opened, j) < at(opened, arena->capacity) implies
                            at(opened, arena->occupied[j]) ==
                                at(clear_occupied.entry, arena->occupied[j])
                    }, k) using {
                        end <= k;
                        k < arena->capacity;
                    }
                    assumption();
                }
                have at(opened, i) < k by auto;
                have at(opened, i) <= k by {
                    apply(int32_less_than_implies_less_equal(at(opened, i), k)) using {
                        at(opened, i) < k;
                    }
                }
                have 0 <= k by {
                    apply(int32_less_equal_transitive(0, at(opened, i), k)) using {
                        0 <= at(opened, i);
                        at(opened, i) <= k;
                    }
                }
                transport(
                    at(opened, arena->occupied[k]) ==
                        at(clear_occupied.entry, arena->occupied[k]),
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
                ) using {
                    at(opened, arena->occupied[k]) ==
                        at(clear_occupied.entry, arena->occupied[k]);
                    at(opened, i) < k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
                    0 <= k;
                    k < arena->capacity;
                }
            }
            let w = fold(arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end), {
                next: at(opened, i) + 1
            });
            have start <= end by {
                apply(int32_less_equal_transitive(start, at(opened, i) + 1, end)) using {
                    start <= at(opened, i) + 1;
                    at(opened, i) + 1 <= end;
                }
            }
            close_invariants by {
                both { normalize(); } and {
                    both { simp(); } and {
                        both { simp(); } and {
                            both { arithmetic() using {
                                at(opened, i) < end;
                                0 <= at(opened, i);
                                end <= arena->capacity;
                                arena->capacity <= 536870911;
                            } } and { arithmetic() using {
                                at(opened, i) < end;
                                0 <= at(opened, i);
                                end <= arena->capacity;
                                arena->capacity <= 536870911;
                            } }
                        }
                    }
                }
            }
        }
    }
    let { next: n } = unfold(w);
    have n <= end;
    have n == i;
    have not (n < end) by { rewrite(n == i); assumption(); }
    have n == end by {
        apply(int32_less_equal_and_not_less_than_implies_equal(n, end)) using { n <= end; not (n < end); }
    }
    execute();
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    simp();
}
```

## Isolation and acceptance

The refusal comes after iterated-target selection, guard checking and hole
selection, at consumption of the separately owned element. A single-store
version without the loop passes recovery checking. Replacing `give`'s legacy
`without_fact` call with `without_fact_incrementally` does not repair the
original arena-free obligation; that experiment was reverted. These findings
do not establish that candidate discovery alone is the cause.

The earlier [descriptor-window reassembly report](archive-descriptor-window-fold-misses-owned-prefix.md)
records a related read/frame boundary at a fold. Treat a common cause as a
hypothesis until checked against both reproductions.

A fix must verify this complete loop proof and the unchanged original
`arena_free` source and contracts. Check fresh, expanded, rewritten and
retained proofs. Preserve rejection of changed pointer cells, wrong slots,
wrong element widths and out-of-range elements. Keep any equality or frame
evidence scoped to its supporting facts, and keep work proportional to the
selected resources rather than scanning unrelated holdings. The full recovery
example audit remains **51/52** until the complete arena project passes.
