resource arena_initialized_storage(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    initialized: int32
) {
    if initialized == 1 {
        contains allocation(data, capacity * 4);
        contains allocation(occupied, capacity * 4);
        fact 1 <= capacity;
        fact capacity <= 536870911;
    }
}

resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

resource arena_state(arena: struct arena*) {
    field live: int32;
    field capacity: int32;
    owns &arena->data;
    owns &arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
    contains arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    );
    owns arena_cells(arena->data, arena->occupied, arena->capacity);
    fact arena->capacity <= 536870911;
    fact arena->capacity == capacity;
    fact arena->live_regions == live;
    fact 0 <= live;
    fact separate(
        memory(arena->occupied[0..arena->capacity]),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(object(arena)),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    );
}

resource arena_region(region: struct region*) {
    field start: int32;
    field end: int32;
    owns object(region);
    owns region->arena->data[start..end];
    fact region->start == start;
    fact region->end == end;
    fact 0 <= start;
    fact start < end;
}

resource arena_window(
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
    owns data[start..next];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact separate(memory(occupied[0..capacity]), memory(data[0..capacity]));
    fact forall (k: int32) {
        next <= k and k < end implies occupied[k] == 0
    };
    fact forall (k: int32) {
        start <= k and k < next implies occupied[k] == 1
    };
}

resource arena_scan(data: int32*, occupied: int32*, capacity: int32) {
    field lo: int32;
    field hi: int32;
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
    fact 0 <= lo;
    fact lo <= hi;
    fact hi <= capacity;
    fact forall (k: int32) {
        lo <= k and k < hi implies occupied[k] == 0
    };
}

spec enum ArenaInitOutcome {
    Failure,
    Success(int32, int32),
}

resource arena_init_outcome(arena: struct arena*) {
    field model: ArenaInitOutcome;
    match model {
        ArenaInitOutcome::Failure => {
            owns object(arena);
        },
        ArenaInitOutcome::Success(live, capacity) => {
            owns state: arena_state(arena);
            fact state.live == live;
            fact state.capacity == capacity;
        },
    }
}

verifying "arena_init.c";

int32 arena_init(struct arena* arena, int32 capacity) {
    consumes object(arena);
    produces outcome: arena_init_outcome(arena);

    ensures result == 0 or result == 1;
    ensures result == 0 implies outcome.model == ArenaInitOutcome::Failure;
    ensures result == 1 implies outcome.model == ArenaInitOutcome::Success(0, capacity);
    ensures forall (k: int32) {
        result == 1 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == 0
    };
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    branch {
        then {
            step();
            let outcome = fold(arena_init_outcome(arena), {
                model: ArenaInitOutcome::Failure
            });
            simp();
        }
        else {}
    }
    branch {
        then {
            step();
            let outcome = fold(arena_init_outcome(arena), {
                model: ArenaInitOutcome::Failure
            });
            simp();
        }
        else {}
    }
    step();
    branch {
        then {
            step();
            let outcome = fold(arena_init_outcome(arena), {
                model: ArenaInitOutcome::Failure
            });
            simp();
        }
        else {}
    }
    step();
    branch {
        then {
            step();
            step();
            let outcome = fold(arena_init_outcome(arena), {
                model: ArenaInitOutcome::Failure
            });
            simp();
        }
        else {}
    }
    have 1 <= capacity by {
        arithmetic() using {
            not (capacity <= 0);
        }
    }
    have capacity <= 536870911 by {
        arithmetic() using {
            not (capacity > 536870911);
        }
    }
    step();
    loop as initialize_occupied {
        decreases capacity - i;
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 0
        };
        owns occupied[0..capacity];

        initialize by simp;
        preserve by {
            mark iteration;
            step();
            step();
            have 0 <= capacity - at(iteration, i) - 1 by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < capacity;
                    1 <= capacity;
                    capacity <= 536870911;
                }
            }
            have capacity - at(iteration, i) - 1 < capacity - at(iteration, i) by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < capacity;
                    1 <= capacity;
                    capacity <= 536870911;
                }
            }
            simp();
        }
    }
    have i == capacity by {
        apply(int32_le_and_not_lt_implies_eq(i, capacity)) using {
            i <= capacity;
            not (i < capacity);
        }
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < capacity);
        instantiate(forall (j: int32) {
            0 <= j and j < i implies occupied[j] == 0
        }, k) using {
            0 <= k;
            k < capacity;
            i == capacity;
        }
        assumption();
    }
    step();
    step();
    step();
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        have k < capacity by {
            assumption();
        }
        instantiate(forall (j: int32) {
            0 <= j and j < capacity implies occupied[j] == 0
        }, k) using {
            0 <= k;
            k < capacity;
        }
        assumption();
    }
    fold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    have 0 <= arena->capacity by {
        simp();
    }
    have arena->capacity <= 1073741823 by {
        arithmetic() using { arena->capacity <= 536870911; }
    }
    have separate(
        memory(arena->occupied[0..arena->capacity]),
        memory(arena->data[0..arena->capacity])
    ) by {
        both {
            both { simp(); } and { assumption(); }
        } and {
            assumption();
        }
    }
    have separate(
        memory(object(arena)),
        memory(arena->data[0..arena->capacity])
    ) by {
        both {
            both { simp(); } and { assumption(); }
        } and {
            assumption();
        }
    }
    have separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    ) by {
        both {
            both { simp(); } and { assumption(); }
        } and {
            assumption();
        }
    }
    gather(arena_cells(arena->data, arena->occupied, arena->capacity));
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    let state = fold(arena_state(arena), { live: 0, capacity: arena->capacity });
    step();
    have result == 1 by {
        normalize();
    }
    have result == 0 or result == 1 by {
        right();
    }
    have forall (k: int32) {
        result == 1 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(result == 1);
        extract(0 <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) {
            0 <= j and j < arena->capacity implies arena->occupied[j] == 0
        }, k) using {
            0 <= k;
            k < arena->capacity;
        }
        assumption();
    }
    let outcome = fold(arena_init_outcome(arena), {
        model: ArenaInitOutcome::Success(0, capacity)
    }, { state: state });
    simp();
}


spec enum ArenaAllocOutcome {
    Failure,
    Success(int32, int32),
}

resource arena_alloc_result(region: struct region*) {
    field model: ArenaAllocOutcome;
    match model {
        ArenaAllocOutcome::Failure => {
            owns object(region);
        },
        ArenaAllocOutcome::Success(start, end) => {
            owns allocated: arena_region(region);
            fact allocated.start == start;
            fact allocated.end == end;
        },
    }
}

verifying "arena_alloc.c";

int32 arena_alloc(struct arena* arena, int32 count, struct region* region) {
    owns st: arena_state(arena);
    consumes object(region);
    produces outcome: arena_alloc_result(region);
    requires st.live < 2147483647;

    ensures result == 0 or result == 1;
    ensures st.live == old(st.live) + result;
    ensures arena->capacity == old(arena->capacity);
    ensures result == 0 implies outcome.model == ArenaAllocOutcome::Failure;
    ensures result == 1 implies outcome.model ==
        ArenaAllocOutcome::Success(region->start, region->end);
    ensures result == 1 implies region->arena == arena;
    ensures result == 1 implies region->end == region->start + count;
    ensures result == 1 implies region->end <= arena->capacity;
} by {
    let { live: n } = unfold(st);
    step();
    step();
    step();
    step();
    branch {
        then {
            step();
            let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
            let outcome = fold(arena_alloc_result(region), {
                model: ArenaAllocOutcome::Failure
            });
            simp();
        }
        else {}
    }
    branch {
        then {
            step();
            let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
            let outcome = fold(arena_alloc_result(region), {
                model: ArenaAllocOutcome::Failure
            });
            simp();
        }
        else {}
    }
    have 0 < count by {
        arithmetic() using { not (count <= 0); }
    }
    have count <= arena->capacity by {
        arithmetic() using { not (count > arena->capacity); }
    }
    unfold(arena_cells(arena->data, arena->occupied, arena->capacity));
    step();
    step();
    have 0 <= arena->capacity by {
        simp();
    }
    have forall (k: int32) {
        0 <= k and k < 0 implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < 0);
        have not (k < 0) by {
            arithmetic() using { 0 <= k; }
        }
        contradiction(k < 0);
    }
    let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), {
        lo: 0, hi: 0
    });
    loop as find_first_free_run {
        decreases arena->capacity - i;
        owns run: arena_scan(arena->data, arena->occupied, arena->capacity);
        invariant run.hi == i;
        invariant run.lo + run_length == i;
        invariant 0 <= run_length and run_length <= count;

        initialize by simp;
        preserve by {
            mark iteration;
            let { lo: lo, hi: hi } = unfold(run);
            have hi == i by {
                simp();
            }
            have lo + run_length == i by {
                simp();
            }
            have lo <= i by {
                simp() using {
                    lo <= hi;
                    hi == i;
                }
            }
            have 0 <= i by {
                apply(int32_le_transitive(0, lo, i)) using {
                    0 <= lo;
                    lo <= i;
                }
            }
            have i + 1 <= arena->capacity by {
                apply(int32_increment_upper_bound(i, arena->capacity)) using {
                    i < arena->capacity;
                }
            }
            if arena->occupied[i] == 0 {
                have run_length + 1 <= count by {
                    apply(int32_increment_upper_bound(run_length, count)) using {
                        run_length < count;
                    }
                }
                branch {
                    then {
                        step();
                    }
                    else {
                        contradiction(not (arena->occupied[i] == 0));
                    }
                }
                step();
                have forall (k: int32) {
                    lo <= k and k < i implies arena->occupied[k] == 0
                } by {
                    intro();
                    intro();
                    extract(lo <= k);
                    extract(k < i);
                    if k < at(iteration, i) {
                        have k < hi by {
                            simp();
                        }
                        instantiate(forall (j: int32) {
                            lo <= j and j < hi implies arena->occupied[j] == 0
                        }, k) using {
                            lo <= k;
                            k < hi;
                        }
                        assumption();
                    } else {
                        have i == at(iteration, i) + 1 by {
                            normalize();
                        }
                        have k < at(iteration, i) + 1 by {
                            rewrite(i == at(iteration, i) + 1);
                            assumption();
                        }
                        have k <= at(iteration, i) by {
                            apply(int32_lt_successor_implies_le(
                                k,
                                at(iteration, i)
                            )) using {
                                k < at(iteration, i) + 1;
                            }
                        }
                        have k == at(iteration, i) by {
                            apply(int32_le_and_not_lt_implies_eq(
                                k,
                                at(iteration, i)
                            )) using {
                                k <= at(iteration, i);
                                not (k < at(iteration, i));
                            }
                        }
                        rewrite(k == at(iteration, i));
                        assumption();
                    }
                }
                have hi == at(iteration, i) by {
                    simp();
                }
                have i == at(iteration, i) + 1 by {
                    normalize();
                }
                have lo <= at(iteration, i) by {
                    simp() using {
                        lo <= hi;
                        hi == at(iteration, i);
                    }
                }
                have at(iteration, i) < at(iteration, i) + 1 by {
                    apply(int32_increment_strictly_increases(
                        at(iteration, i),
                        at(iteration, arena->capacity)
                    )) using {
                        at(iteration, i) < at(iteration, arena->capacity);
                    }
                }
                have at(iteration, i) < i by {
                    rewrite(i == at(iteration, i) + 1);
                    assumption();
                }
                have at(iteration, i) <= i by {
                    apply(int32_lt_implies_le(at(iteration, i), i)) using {
                        at(iteration, i) < i;
                    }
                }
                have lo <= i by {
                    apply(int32_le_transitive(lo, at(iteration, i), i)) using {
                        lo <= at(iteration, i);
                        at(iteration, i) <= i;
                    }
                }
                have i <= arena->capacity by {
                    simp();
                }
                have run_length == at(iteration, run_length) + 1 by {
                    normalize();
                }
                have lo + at(iteration, run_length) == at(iteration, i) by {
                    simp();
                }
                have lo + run_length == i by {
                    rewrite(run_length == at(iteration, run_length) + 1);
                    rewrite(i == at(iteration, i) + 1);
                    simp();
                }
                have 0 <= run_length and run_length <= count by {
                    simp();
                }
                let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), {
                    lo: lo, hi: i
                });
                have run.hi == i by {
                    simp();
                }
                have run.lo + run_length == i by {
                    simp();
                }
                have 0 <= at(iteration, i) by {
                    assumption();
                }
                have 0 <= 0 - at(iteration, i) + arena->capacity - 1 by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, arena->capacity);
                        0 <= arena->capacity;
                    }
                }
                have 0 - at(iteration, i) + arena->capacity - 1
                    < 0 - at(iteration, i) + arena->capacity by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, arena->capacity);
                        0 <= arena->capacity;
                    }
                }
                close_invariants();
            } else {
                branch {
                    then {
                        contradiction(arena->occupied[i] == 0);
                    }
                    else {
                        step();
                    }
                }
                step();
                have forall (k: int32) {
                    i <= k and k < i implies arena->occupied[k] == 0
                } by {
                    intro();
                    intro();
                    extract(i <= k);
                    extract(k < i);
                    have not (k < i) by {
                        arithmetic() using { i <= k; }
                    }
                    contradiction(k < i);
                }
                have 0 <= i by { simp(); }
                have i <= arena->capacity by { simp(); }
                let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), {
                    lo: i, hi: i
                });
                have 0 <= at(iteration, i) by {
                    assumption();
                }
                have 0 <= 0 - at(iteration, i) + arena->capacity - 1 by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, arena->capacity);
                        0 <= arena->capacity;
                    }
                }
                have 0 - at(iteration, i) + arena->capacity - 1
                    < 0 - at(iteration, i) + arena->capacity by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, arena->capacity);
                        0 <= arena->capacity;
                    }
                }
                close_invariants();
            }
        }
    }
    let { lo: run_lo, hi: run_hi } = unfold(run);
    branch {
        then {
            fold(arena_cells(arena->data, arena->occupied, arena->capacity));
            step();
            let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
            let outcome = fold(arena_alloc_result(region), {
                model: ArenaAllocOutcome::Failure
            });
            simp();
        }
        else {}
    }
    have run_length == count by {
        apply(int32_le_and_not_lt_implies_eq(run_length, count)) using {
            run_length <= count;
            not (run_length < count);
        }
    }
    have count == run_length by {
        simp();
    }
    have run_lo + count == i by {
        rewrite(count == run_length);
        assumption();
    }
    have 0 <= count by {
        apply(int32_lt_implies_le(0, count)) using { 0 < count; }
    }
    have defined(run_lo + count) by {
        simp();
    }
    have count <= run_lo + count by {
        apply(int32_add_nonnegative_left_is_at_least_right(run_lo, count)) using {
            0 <= run_lo;
            defined(run_lo + count);
        }
    }
    have i == run_lo + count by {
        simp();
    }
    have count <= i by {
        rewrite(i == run_lo + count);
        assumption();
    }
    have defined(i - count) by {
        apply(int32_nonnegative_subtract_within_value_is_defined(i, count)) using {
            0 <= count;
            count <= i;
        }
    }
    step();
    have start == run_lo by {
        simp();
    }
    step();
    have end == i by {
        normalize();
    }
    have run_lo <= arena->capacity by {
        apply(int32_le_transitive(run_lo, run_hi, arena->capacity)) using {
            run_lo <= run_hi;
            run_hi <= arena->capacity;
        }
    }
    have start < end by {
        rewrite(start == run_lo);
        rewrite(end == i);
        rewrite(i == run_lo + count);
        arithmetic() using {
            0 < count;
            0 <= run_lo;
            run_lo <= arena->capacity;
            count <= arena->capacity;
            arena->capacity <= 536870911;
        }
    }
    have forall (k: int32) {
        start <= k and k < end implies arena->occupied[k] == 0
    } by {
        rewrite(start == run_lo);
        rewrite(end == i);
        simp();
    }
    step();
    have i == start by {
        normalize();
    }
    have 0 <= start by {
        simp();
    }
    have start <= end by {
        simp();
    }
    have end <= arena->capacity by {
        simp();
    }
    have forall (k: int32) {
        start <= k and k < start implies arena->occupied[k] == 1
    } by {
        intro();
        intro();
        extract(start <= k);
        extract(k < start);
        have not (k < start) by {
            arithmetic() using { start <= k; }
        }
        contradiction(k < start);
    }
    let w = fold(arena_window(
        arena->data,
        arena->occupied,
        arena->capacity,
        start,
        end
    ), {
        next: start
    });
    loop as mark_free_run {
        decreases end - i;
        owns w: arena_window(
            arena->data,
            arena->occupied,
            arena->capacity,
            start,
            end
        );
        invariant w.next == i;

        initialize by simp;
        preserve by {
            let { next: m } = unfold(w);
            have m == i by simp;
            have m <= i by simp;
            have i < end by simp;
            have end <= arena->capacity by simp;
            have arena->occupied[i] == 0 by {
                instantiate(forall (k: int32) {
                    m <= k and k < end implies arena->occupied[k] == 0
                }, i) using {
                    m <= i;
                    i < end;
                }
                assumption();
            }
            take(arena->data[i..i + 1]);
            have start <= i by simp;
            have 0 <= i by simp;
            have i < arena->capacity by simp;
            mark opened;
            step();
            have forall (k: int32) {
                at(opened, i) + 1 <= k and k < end implies
                    arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(at(opened, i) + 1 <= k);
                extract(k < end);
                apply(int32_increment_strictly_increases(at(opened, i), end)) using {
                    at(opened, i) < end;
                }
                apply(int32_successor_le_implies_lt(at(opened, i), k)) using {
                    at(opened, i) < at(opened, i) + 1;
                    at(opened, i) + 1 <= k;
                }
                apply(int32_lt_implies_le(at(opened, i), k)) using {
                    at(opened, i) < k;
                }
                have m <= k by {
                    rewrite(m == i);
                    assumption();
                }
                have at(opened, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) {
                        at(opened, m) <= at(opened, j) and
                            at(opened, j) < at(opened, end) implies
                            at(opened, arena->occupied[j]) == at(opened, 0)
                    }, k) using {
                        m <= k;
                        k < end;
                    }
                    assumption();
                }
                have 0 <= k by {
                    apply(int32_le_transitive(0, at(opened, i), k)) using {
                        0 <= at(opened, i);
                        at(opened, i) <= k;
                    }
                }
                have k < at(opened, arena->capacity) by {
                    apply(int32_lt_le_transitive(k, end, at(opened, arena->capacity))) using {
                        k < end;
                        end <= at(opened, arena->capacity);
                    }
                }
                transport(
                    at(opened, arena->occupied[k]) == 0,
                    arena->occupied[k] == 0
                ) using {
                    at(opened, arena->occupied[k]) == 0;
                    at(opened, i) < k;
                    0 <= at(opened, i);
                    at(opened, i) < at(opened, arena->capacity);
                    0 <= k;
                    k < at(opened, arena->capacity);
                }
                assumption();
            }
            have forall (k: int32) {
                start <= k and k < at(opened, i) + 1 implies
                    arena->occupied[k] == 1
            } by {
                intro();
                intro();
                extract(start <= k);
                extract(k < at(opened, i) + 1);
                if k < at(opened, i) {
                    have k < m by {
                        simp();
                    }
                    have at(opened, arena->occupied[k]) == 1 by {
                        instantiate(forall (j: int32) {
                            at(opened, start) <= at(opened, j) and
                                at(opened, j) < at(opened, m) implies
                                at(opened, arena->occupied[j]) == at(opened, 1)
                        }, k) using {
                            start <= k;
                            k < m;
                        }
                        assumption();
                    }
                    have 0 <= k by simp;
                    transport(
                        at(opened, arena->occupied[k]) == 1,
                        arena->occupied[k] == 1
                    ) using {
                        at(opened, arena->occupied[k]) == 1;
                        k < at(opened, i);
                        0 <= k;
                        0 <= at(opened, i);
                        at(opened, i) < arena->capacity;
                    }
                } else {
                    have k <= at(opened, i) by {
                        apply(int32_lt_successor_implies_le(k, at(opened, i))) using {
                            k < at(opened, i) + 1;
                        }
                    }
                    have k == at(opened, i) by {
                        apply(int32_le_and_not_lt_implies_eq(k, at(opened, i))) using {
                            k <= at(opened, i);
                            not (k < at(opened, i));
                        }
                    }
                    rewrite(k == at(opened, i));
                    normalize();
                }
            }
            step();
            let w = fold(arena_window(
                arena->data,
                arena->occupied,
                arena->capacity,
                start,
                end
            ), {
                next: at(opened, i) + 1
            });
            have 0 <= end - at(opened, i) - 1 by {
                arithmetic() using {
                    at(opened, i) < end;
                    0 <= at(opened, i);
                    end <= arena->capacity;
                }
            }
            have end - at(opened, i) - 1 < end - at(opened, i) by {
                arithmetic() using {
                    at(opened, i) < end;
                    0 <= at(opened, i);
                    end <= arena->capacity;
                }
            }
            close_invariants();
        }
    }
    let { next: m } = unfold(w);
    have m <= end by {
        simp();
    }
    have m == i by {
        simp();
    }
    have not (m < end) by {
        rewrite(m == i);
        assumption();
    }
    have m == end by {
        apply(int32_le_and_not_lt_implies_eq(m, end)) using {
            m <= end;
            not (m < end);
        }
    }
    step();
    step();
    step();
    have arena->live_regions == n by {
        simp();
    }
    have n < 2147483647 by {
        simp();
    }
    have defined(n + 1) by {
        apply(int32_increment_below_max_is_defined(n)) using {
            n < 2147483647;
        }
    }
    step();
    have region->start == start by {
        simp();
    }
    have region->end == end by {
        simp();
    }
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    let allocated = fold(arena_region(region), { start: start, end: end });
    let st = fold(arena_state(arena), { live: n + 1, capacity: arena->capacity });
    let outcome = fold(arena_alloc_result(region), {
        model: ArenaAllocOutcome::Success(start, end)
    }, { allocated: allocated });
    step();
    have result == 1 by {
        normalize();
    }
    simp();
}

verifying "arena_write.c";

void arena_write(struct region* region, int32 index, int32 value) {
    owns r: arena_region(region);
    owns st: arena_state(region->arena);
    requires 0 <= index;
    requires defined(r.start + index) and r.start + index < r.end;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures st.capacity == old(st.capacity);
    ensures st.live == old(st.live);
    ensures region->arena == old(region->arena);
    ensures region->arena->data[region->start + index] == value;
} by {
    let { live: n, capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have defined(s + index) by {
        simp() using {
            defined(s + index) and s + index < e;
        }
    }
    have s + index < e by {
        simp() using {
            defined(s + index) and s + index < e;
        }
    }
    have s <= s + index by {
        apply(int32_add_nonnegative_right_is_at_least_left(s, index)) using {
            0 <= index;
            defined(s + index);
        }
    }
    have s + index + 1 <= e by {
        apply(int32_increment_upper_bound(s + index, e)) using {
            s + index < e;
        }
    }
    have region->start == s by {
        assumption();
    }
    have defined(region->start + index) by {
        rewrite(region->start == s);
        assumption();
    }
    have region->start <= region->start + index by {
        rewrite(region->start == s);
        assumption();
    }
    have region->start + index + 1 <= e by {
        rewrite(region->start == s);
        assumption();
    }
    execute();
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
    simp();
}

verifying "arena_read.c";

int32 arena_read(struct region* region, int32 index) {
    owns r: arena_region(region);
    owns st: arena_state(region->arena);
    requires 0 <= index;
    requires defined(r.start + index) and r.start + index < r.end;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures st.capacity == old(st.capacity);
    ensures st.live == old(st.live);
    ensures region->arena == old(region->arena);
    ensures result == region->arena->data[region->start + index];
} by {
    let { live: n, capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have defined(s + index) by {
        simp() using {
            defined(s + index) and s + index < e;
        }
    }
    have s + index < e by {
        simp() using {
            defined(s + index) and s + index < e;
        }
    }
    have s <= s + index by {
        apply(int32_add_nonnegative_right_is_at_least_left(s, index)) using {
            0 <= index;
            defined(s + index);
        }
    }
    have s + index + 1 <= e by {
        apply(int32_increment_upper_bound(s + index, e)) using {
            s + index < e;
        }
    }
    have region->start == s by {
        assumption();
    }
    have defined(region->start + index) by {
        rewrite(region->start == s);
        assumption();
    }
    have region->start <= region->start + index by {
        rewrite(region->start == s);
        assumption();
    }
    have region->start + index + 1 <= e by {
        rewrite(region->start == s);
        assumption();
    }
    execute();
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
    simp();
}

verifying "arena_destroy.c";

void arena_destroy(struct arena* arena) {
    consumes st: arena_state(arena);
    requires forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    };
    produces object(arena);

    ensures arena->data == 0;
    ensures arena->occupied == 0;
    ensures arena->capacity == 0;
    ensures arena->live_regions == 0;
} by {
    let { live: n } = unfold(st);
    unfold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    unfold(arena_cells(arena->data, arena->occupied, arena->capacity));
    scatter(arena_cells(arena->data, arena->occupied, arena->capacity));
    execute();
    simp();
}

verifying "arena_region_length.c";

int32 arena_region_length(struct region* region) {
    owns r: arena_region(region);
    owns st: arena_state(region->arena);
    ensures result == r.end - r.start;
    ensures st.live == old(st.live);
    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
} by {
    let { live: n } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have region->start == s by { assumption(); }
    have region->end == e by { assumption(); }
    execute();
    have result == e - s by {
        simp() using { result == region->end - region->start; region->start == s; region->end == e; }
    }
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: region->arena->capacity });
    simp();
}
