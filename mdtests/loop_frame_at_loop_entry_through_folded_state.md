# Framing against the loop entry through a folded state's field

The loop-entry form of `loop_frame_through_folded_state_field_cells.md`: the
frame is `arena->occupied[k] == at(mark.entry, arena->occupied[k])`, and the
state is unfolded first. `examples/arena` frames its scan, mark, and clear
loops this way, because its map is never viewable at the function entry: it
is owned by a child of the folded state.

The bundle's map members are then one at the back edge and one at the loop
entry. The proof states the map's viewability just before the loop, and the
explicit closer transports it to both. The whole bundle has no one source
form, since synthesis names only the iteration entry beside the current
state, so a written `both` spells each member on its own, the way the smart
closer spells the leaf it closes; before that, the members had no spelling
at all and `intro` could not name the quantified index.

```c filename=loop_frame_folded_state_loop_entry.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

void mark_run(struct arena* arena, int32 start, int32 end) {
    int32 i;
    arena->occupied[start] = 0;
    i = start;
    while (i < end) {
        arena->occupied[i] = 1;
        i = i + 1;
    }
}
```

```click
resource window(occupied: int32*, capacity: int32, start: int32, end: int32) {
    field next: int32;
    owns occupied[0..capacity];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact forall (k: int32) {
        start <= k and k < next implies occupied[k] == 1
    };
}

resource state(arena: struct arena*) {
    field capacity: int32;
    owns &arena->data;
    owns &arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
    fact arena->capacity == capacity;
    fact separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    );
}

verifying "loop_frame_folded_state_loop_entry.c";

void mark_run(struct arena* arena, int32 start, int32 end) {
    owns st: state(arena);
    consumes w: window(arena->occupied, arena->capacity, start, end);
    requires w.next == start;
    requires start < end;
} by {
    let { capacity: c } = unfold(st);
    let { next: n0 } = unfold(w);
    have 0 <= start by {
        assumption();
    }
    have start < arena->capacity by {
        extract(at(function.entry, 0) <= at(function.entry, arena->capacity));
        extract(at(function.entry, arena->capacity) <= at(function.entry, 1073741823));
        apply(int32_lt_le_transitive(at(function.entry, start), at(function.entry, end), at(function.entry, arena->capacity))) using {
            at(function.entry, start) < at(function.entry, end);
            at(function.entry, end) <= at(function.entry, arena->capacity);
        }
    }
    step();
    step();
    have arena->occupied[start] == 0 by {
        normalize();
    }
    step();
    have viewable(arena->occupied[0..arena->capacity]) by {
        extract(at(function.entry, 0) <= at(function.entry, arena->capacity));
        extract(at(function.entry, arena->capacity) <= at(function.entry, 1073741823));
        transport(at(statement(0).entry, viewable(arena->occupied[0..load_int32(byte_offset(arena, 16))])), viewable(arena->occupied[0..arena->capacity])) using {
            at(statement(0).entry, viewable(arena->occupied[0..load_int32(byte_offset(arena, 16))]));
        }
    }
    let w = fold(window(arena->occupied, arena->capacity, start, end), { next: start });
    loop as mark {
        decreases (end - i);
        owns w: window(arena->occupied, arena->capacity, start, end);
        invariant w.next == i;
        invariant forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark.entry, arena->occupied[k]) };
        initialize by {
            have w.next == i by {
                have forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    extract(0 <= k);
                    extract(k < start);
                    transport(at(mark.entry, arena->occupied[k]) == at(mark.entry, arena->occupied[k]), arena->occupied[k] == at(mark.entry, arena->occupied[k])) using {
                        0 <= k;
                        k < start;
                    }
                }
                normalize();
            }
            have forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark.entry, arena->occupied[k]) } by {
                have forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    extract(0 <= k);
                    extract(k < start);
                    transport(at(mark.entry, arena->occupied[k]) == at(mark.entry, arena->occupied[k]), arena->occupied[k] == at(mark.entry, arena->occupied[k])) using {
                        0 <= k;
                        k < start;
                    }
                }
                assumption();
            }
        }
        preserve by {
            let { next: m } = unfold(w);
            have m == i by {
                assumption();
            }
            have i < end by {
                assumption();
            }
            have start <= m by {
                assumption();
            }
            have 0 <= m by {
                apply(int32_le_transitive(0, start, m)) using {
                    0 <= start;
                    start <= m;
                }
            }
            have 0 <= i by {
                rewrite(i == m);
                assumption();
            }
            have i < arena->capacity by {
                apply(int32_lt_le_transitive(i, end, arena->capacity)) using {
                    i < end;
                    end <= arena->capacity;
                }
            }
            mark opened;
            step();
            step();
            have forall (k: int32) { start <= k and k < (at(opened, i) + 1) implies arena->occupied[k] == 1 } by {
                intro();
                intro();
                extract(start <= k);
                extract(k < (at(opened, i) + 1));
                if k < at(opened, i) {
                    have k < m by {
                        rewrite(at(statement(5).entry, m) == at(statement(5).entry, i));
                        assumption();
                    }
                    have at(opened, arena->occupied[k]) == 1 by {
                        instantiate(forall (j: int32) { at(opened, start) <= at(opened, j) and at(opened, j) < at(opened, m) implies at(opened, arena->occupied[j]) == at(opened, 1) }, k) using {
                            start <= k;
                            k < m;
                        }
                        assumption();
                    }
                    have 0 <= k by {
                        extract(at(function.entry, 0) <= at(function.entry, arena->capacity));
                        extract(at(function.entry, arena->capacity) <= at(function.entry, 1073741823));
                        apply(int32_le_transitive(at(function.entry, 0), at(function.entry, start), k)) using {
                            at(function.entry, 0) <= at(function.entry, start);
                            start <= k;
                        }
                    }
                    transport(at(opened, arena->occupied[k]) == 1, arena->occupied[k] == 1) using {
                        at(opened, arena->occupied[k]) == 1;
                        k < at(opened, i);
                        0 <= k;
                        0 <= at(opened, i);
                        at(opened, i) < arena->capacity;
                    }
                } else {
                    have k <= at(opened, i) by {
                        apply(int32_lt_successor_implies_le(k, at(opened, i))) using {
                            k < (at(opened, i) + 1);
                        }
                    }
                    have k == at(opened, i) by {
                        apply(int32_le_and_not_lt_implies_eq(k, at(opened, i))) using {
                            k <= at(opened, i);
                            not k < at(opened, i);
                        }
                    }
                    rewrite(k == at(opened, i));
                    normalize();
                }
            }
            have start <= at(opened, i) by {
                rewrite(at(opened, i) == m);
                assumption();
            }
            have forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark.entry, arena->occupied[k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < start);
                have at(opened, arena->occupied[k]) == at(mark.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { at(opened, 0) <= at(opened, j) and at(opened, j) < at(opened, start) implies at(opened, arena->occupied[j]) == at(mark.entry, arena->occupied[j]) }, k) using {
                        0 <= k;
                        k < start;
                    }
                    assumption();
                }
                have k < at(opened, i) by {
                    apply(int32_lt_le_transitive(k, start, at(opened, i))) using {
                        k < start;
                        start <= at(opened, i);
                    }
                }
                transport(at(opened, arena->occupied[k]) == at(mark.entry, arena->occupied[k]), arena->occupied[k] == at(mark.entry, arena->occupied[k])) using {
                    at(opened, arena->occupied[k]) == at(mark.entry, arena->occupied[k]);
                    k < at(opened, i);
                    0 <= k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
                }
            }
            have start <= (at(opened, i) + 1) by {
                apply(int32_increment_lower_bound(at(opened, i), start, end)) using {
                    start <= at(opened, i);
                    at(opened, i) < end;
                }
            }
            have (at(opened, i) + 1) <= end by {
                apply(int32_increment_upper_bound(at(opened, i), end)) using {
                    at(opened, i) < end;
                }
            }
            let w = fold(window(arena->occupied, arena->capacity, start, end), { next: (at(opened, i) + 1) });
            have 0 <= ((end - at(opened, i)) - 1) by {
                arithmetic_certificate signed_int32 {
                    premise 0: at(opened, i) < end => at(opened, i) < end;
                    premise 1: 0 <= at(opened, i) => 0 <= at(opened, i);
                    add 0, 1 => (at(opened, i) + 0) < (end + at(opened, i));
                    interval_from_affine 2 (end) (1) (2147483647);
                    interval_from_affine 1 (at(opened, i)) (0) (2147483647);
                    interval_subtract 3, 4 3 (-2147483646) (2147483647);
                    interval_atom (1) (1) (1);
                    interval_subtract 5, 6 5 (-2147483647) (2147483646);
                    affine_conclusion 0 7 => 0 <= ((end - at(opened, i)) - 1);
                    conclusion 8;
                }
            }
            have ((end - at(opened, i)) - 1) < (end - at(opened, i)) by {
                arithmetic_certificate signed_int32 {
                    premise 0: at(statement(4).entry, i) < at(statement(4).entry, end) => at(statement(4).entry, i) < at(statement(4).entry, end);
                    premise 1: at(statement(4).entry, 0) <= at(statement(4).entry, i) => at(statement(4).entry, 0) <= at(statement(4).entry, i);
                    add 0, 1 => (at(statement(4).entry, i) + at(statement(4).entry, 0)) < (at(statement(4).entry, end) + at(statement(4).entry, i));
                    interval_from_affine 2 (end) (1) (2147483647);
                    interval_from_affine 1 (at(statement(4).entry, i)) (0) (2147483647);
                    interval_subtract 3, 4 3 (-2147483646) (2147483647);
                    interval_atom (1) (1) (1);
                    interval_subtract 5, 6 5 (-2147483647) (2147483646);
                    interval_subtract 3, 4 3 (-2147483646) (2147483647);
                    trivial => 0 <= 0;
                    affine_conclusion_pair 9 7 8 => ((end - at(opened, i)) - 1) < (end - at(opened, i));
                    conclusion 10;
                }
            }
            close_invariants by {
                both {
                    normalize();
                } and {
                    both {
                        intro();
                        assumption();
                    } and {
                        split();
                    }
                }
            }
        }
    }
    let { next: n } = unfold(w);
    step();
    let st = fold(state(arena), { capacity: c });
    assumption();
}
```

```expect
pass
```
