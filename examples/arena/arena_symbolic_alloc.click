spec enum ArenaPrefixAllocOutcome {
    Failure(int32, int32),
    Success(int32, int32, int32, int32),
}

resource arena_prefix_partition(
    data: int32*,
    occupied: int32*,
    capacity: int32
) {
    field prefix: int32;
    owns occupied[0..capacity];
    owns data[prefix..capacity];
    fact 0 <= prefix;
    fact prefix <= capacity;
    fact forall (k: int32) {
        0 <= k and k < prefix implies occupied[k] == 1
    };
    fact forall (k: int32) {
        prefix <= k and k < capacity implies occupied[k] == 0
    };
}

resource arena_prefix_state(arena: struct arena*) {
    field prefix: int32;
    field live: int32;
    owns &arena->data;
    owns &arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
    owns partition: arena_prefix_partition(
        arena->data,
        arena->occupied,
        arena->capacity
    );
    fact partition.prefix == prefix;
    fact arena->capacity <= 536870911;
    fact arena->live_regions == live;
    fact 0 <= live;
    fact live <= prefix;
    fact separate(
        memory(object(arena)),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    );
}

resource arena_prefix_region(region: struct region*) {
    field start: int32;
    field end: int32;
    owns object(region);
    owns region->arena->data[start..end];
    fact region->start == start;
    fact region->end == end;
    fact 0 <= start;
    fact start < end;
}

resource arena_prefix_alloc_result(
    arena: struct arena*,
    region: struct region*
) {
    field model: ArenaPrefixAllocOutcome;
    match model {
        ArenaPrefixAllocOutcome::Failure(prefix, live) => {
            owns state: arena_prefix_state(arena);
            owns object(region);
            fact state.prefix == prefix;
            fact state.live == live;
        },
        ArenaPrefixAllocOutcome::Success(prefix, live, start, end) => {
            owns state: arena_prefix_state(arena);
            owns allocated: arena_prefix_region(region);
            fact state.prefix == prefix;
            fact state.live == live;
            fact allocated.start == start;
            fact allocated.end == end;
        },
    }
}

verifying "arena_alloc.c";

int32 arena_alloc(struct arena* arena, int32 count, struct region* region) {
    consumes before: arena_prefix_state(arena);
    consumes object(region);
    produces outcome: arena_prefix_alloc_result(arena, region);

    ensures result == 0 or result == 1;
    ensures result == 0 implies outcome.model ==
        ArenaPrefixAllocOutcome::Failure(old(before.prefix), old(before.live));
    ensures result == 1 implies outcome.model ==
        ArenaPrefixAllocOutcome::Success(
            old(before.prefix) + count,
            old(before.live) + 1,
            old(before.prefix),
            old(before.prefix) + count
        );
    ensures result == 1 implies region->arena == arena;
    ensures result == 1 implies region->start == old(before.prefix);
    ensures result == 1 implies region->end == region->start + count;
    ensures result == 1 implies arena->live_regions == old(before.live) + 1;
} by {
    let { partition: partition, prefix: p, live: n } = unfold(before);
    step();
    step();
    step();
    step();
    branch {
        then {
            step();
            let restored = fold(arena_prefix_state(arena), {
                prefix: p, live: n
            }, { partition: partition });
            let outcome = fold(arena_prefix_alloc_result(arena, region), {
                model: ArenaPrefixAllocOutcome::Failure(p, n)
            }, { state: restored });
            simp();
        }
        else {}
    }
    branch {
        then {
            step();
            let restored = fold(arena_prefix_state(arena), {
                prefix: p, live: n
            }, { partition: partition });
            let outcome = fold(arena_prefix_alloc_result(arena, region), {
                model: ArenaPrefixAllocOutcome::Failure(p, n)
            }, { state: restored });
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
    have 0 <= count by {
        apply(int32_lt_implies_le(0, count)) using { 0 < count; }
    }
    unfold(partition);
    step();
    step();
    loop as find_first_free_run {
        decreases arena->capacity - i;
        invariant 0 <= i and i <= arena->capacity;
        invariant 0 <= run_length and run_length <= count;
        invariant (i <= p and run_length == 0) or
            (p <= i and p + run_length == i);
        owns arena->occupied[0..arena->capacity];

        initialize by simp;
        preserve by {
            mark iteration;
            if i < p {
                have arena->occupied[i] == 1 by {
                    instantiate(forall (k: int32) {
                        0 <= k and k < p implies
                            arena->occupied[k] == 1
                    }, i) using {
                        0 <= i;
                        i < p;
                    }
                    assumption();
                }
                have i + 1 <= p by {
                    apply(int32_increment_upper_bound(
                        i,
                        p
                    )) using {
                        i < p;
                    }
                    assumption();
                }
                branch {
                    then { contradiction(arena->occupied[i] == 0); }
                    else {
                        step();
                    }
                }
                step();
                have 0 <= i and i <= arena->capacity by {
                    simp();
                }
                have 0 <= run_length and run_length <= count by {
                    simp();
                }
                have i <= p and run_length == 0 by {
                    simp();
                }
                have (i <= p and run_length == 0) or
                    (p <= i and p + run_length == i) by {
                    left();
                }
                have 0 <= at(iteration, i) by {
                    simp();
                }
                have 0 <= arena->capacity by {
                    simp();
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
                close_invariants by {
                    split();
                }
            } else {
                have p <= i by {
                    arithmetic() using { not (i < p); }
                }
                have p + run_length == i by {
                    cases(
                        (i <= p and run_length == 0) or
                            (p <= i and p + run_length == i)
                    ) {
                        extract(i <= p);
                        extract(run_length == 0);
                        have i == p by {
                            apply(int32_le_and_not_lt_implies_eq(
                                i,
                                p
                            )) using {
                                i <= p;
                                not (i < p);
                            }
                            assumption();
                        }
                        rewrite(run_length == 0);
                        rewrite(i == p);
                        normalize();
                    } {
                        extract(p + run_length == i);
                        assumption();
                    }
                }
                have arena->occupied[i] == 0 by {
                    instantiate(forall (k: int32) {
                        p <= k and k < arena->capacity implies
                            arena->occupied[k] == 0
                    }, i) using {
                        p <= i;
                        i < arena->capacity;
                    }
                    assumption();
                }
                have i + 1 <= arena->capacity by {
                    apply(int32_increment_upper_bound(
                        i,
                        arena->capacity
                    )) using {
                        i < arena->capacity;
                    }
                    assumption();
                }
                have run_length + 1 <= count by {
                    apply(int32_increment_upper_bound(
                        run_length,
                        count
                    )) using {
                        run_length < count;
                    }
                    assumption();
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
                have 0 <= i and i <= arena->capacity by {
                    simp();
                }
                have 0 <= run_length and run_length <= count by {
                    simp();
                }
                have p <= i and p + run_length == i by {
                    simp();
                }
                have (i <= p and run_length == 0) or
                    (p <= i and p + run_length == i) by {
                    right();
                }
                have 0 <= at(iteration, i) by {
                    simp();
                }
                have 0 <= arena->capacity by {
                    simp();
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
                close_invariants by {
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
    branch {
        then {
            step();
            let partition = fold(arena_prefix_partition(
                arena->data,
                arena->occupied,
                arena->capacity
            ), {
                prefix: p
            });
            let restored = fold(arena_prefix_state(arena), {
                prefix: p, live: n
            }, { partition: partition });
            let outcome = fold(arena_prefix_alloc_result(arena, region), {
                model: ArenaPrefixAllocOutcome::Failure(p, n)
            }, { state: restored });
            simp();
        }
        else {}
    }
    have run_length <= count by {
        simp() using {
            0 <= run_length and run_length <= count;
        }
    }
    have run_length == count by {
        apply(int32_le_and_not_lt_implies_eq(
            run_length,
            count
        )) using {
            run_length <= count;
            not (run_length < count);
        }
        assumption();
    }
    have p + run_length == i by {
        cases(
            (i <= p and run_length == 0) or
                (p <= i and p + run_length == i)
        ) {
            extract(run_length == 0);
            have not (run_length == 0) by {
                rewrite(run_length == count);
                arithmetic() using { 0 < count; }
            }
            contradiction(run_length == 0);
        } {
            extract(p + run_length == i);
            assumption();
        }
    }
    have i == p + count by {
        have count == run_length by {
            simp() using { run_length == count; }
        }
        rewrite(count == run_length);
        simp() using { p + run_length == i; }
    }
    step();
    have start == p by {
        simp() using { i == p + count; }
    }
    step();
    have end == p + count by {
        simp() using { i == p + count; }
    }
    have end <= arena->capacity by {
        simp() using {
            end == i;
            0 <= i and i <= arena->capacity;
        }
    }
    step();
    have i == start by {
        normalize();
    }
    have 0 <= start by {
        rewrite(start == p);
        assumption();
    }
    have start <= i and i <= end by {
        have start <= i by {
            rewrite(i == start);
            normalize();
        }
        have i <= end by {
            rewrite(i == start);
            rewrite(start == p);
            rewrite(end == p + count);
            arithmetic() using {
                0 <= p;
                p <= arena->capacity;
                arena->capacity <= 536870911;
                0 < count;
                count <= arena->capacity;
            }
        }
        split();
    }
    mark before_mark;
    loop as mark_free_run {
        decreases end - i;
        invariant start <= i and i <= end;
        invariant forall (k: int32) {
            start <= k and k < i implies arena->occupied[k] == 1
        };
        owns arena->occupied[start..end];

        initialize by {
            have start <= i and i <= end by {
                assumption();
            }
            have forall (k: int32) {
                start <= k and k < i implies
                    arena->occupied[k] == 1
            } by {
                intro();
                intro();
                extract(start <= k);
                extract(k < i);
                have not (k < i) by {
                    arithmetic() using {
                        start <= k;
                        i == start;
                    }
                }
                contradiction(k < i);
            }
        }
        preserve by {
            mark iteration;
            have i + 1 <= end by {
                apply(int32_increment_upper_bound(i, end)) using { i < end; }
            }
            have start <= i + 1 by {
                apply(int32_increment_lower_bound(i, start, end)) using {
                    start <= i;
                    i < end;
                }
            }
            step();
            step();
            have 0 <= at(iteration, i) by {
                arithmetic() using {
                    0 <= start;
                    start <= at(iteration, i);
                }
            }
            have 0 <= end by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < end;
                }
            }
            have 0 <= end - at(iteration, i) - 1 by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    0 <= end;
                    at(iteration, i) < end;
                }
            }
            have end - at(iteration, i) - 1 < end - at(iteration, i) by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    0 <= end;
                    at(iteration, i) < end;
                }
            }
            have i == at(iteration, i) + 1 by {
                normalize();
            }
            have start <= i and i <= end by {
                rewrite(i == at(iteration, i) + 1);
                split();
            }
            have forall (k: int32) {
                start <= k and k < i implies
                    arena->occupied[k] == 1
            } by {
                intro();
                intro();
                extract(start <= k);
                extract(k < i);
                if k < at(iteration, i) {
                    have k != at(iteration, i) by {
                        apply(int32_lt_implies_neq(
                            k,
                            at(iteration, i)
                        )) using {
                            k < at(iteration, i);
                        }
                    }
                    have at(iteration, arena->occupied[k]) == 1 by {
                        instantiate(forall (j: int32) {
                            at(iteration, start) <= at(iteration, j) and
                                at(iteration, j) < at(iteration, i) implies
                                at(iteration, arena->occupied[j]) ==
                                    at(iteration, 1)
                        }, k) using {
                            start <= k;
                            k < at(iteration, i);
                        }
                        assumption();
                    }
                    transport(
                        at(iteration, arena->occupied[k]) == 1,
                        arena->occupied[k] == 1
                    ) using {
                        at(iteration, arena->occupied[k]) == 1;
                        start <= k;
                        k < at(iteration, i);
                        k != at(iteration, i);
                    }
                } else {
                    have i == at(iteration, i) + 1 by {
                        simp();
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
                    normalize();
                }
            }
            close_invariants by {
                both {
                    intro();
                    intro();
                    simp();
                } and {
                    both {
                        intro();
                        intro();
                        instantiate(forall (k: int32) {
                            start <= k and k < i implies
                                arena->occupied[k] == 1
                        }, __click_q0) using {
                            start <= __click_q0 and __click_q0 < i;
                        }
                        transport(
                            arena->occupied[__click_q0] == 1,
                            viewable((load_int32_pointer(
                                byte_offset(arena, 8)
                            ) + __click_q0)[0..1])
                        ) using {
                            arena->occupied[__click_q0] == 1;
                            start <= __click_q0 and __click_q0 < i;
                            start <= i and i <= end;
                            0 <= start;
                            end <= arena->capacity;
                            arena->capacity <= 536870911;
                        }
                    } and {
                        both {
                            intro();
                            intro();
                            assumption();
                        } and {
                            both {
                                assumption();
                            } and {
                                assumption();
                            }
                        }
                    }
                }
            }
        }
    }
    have i == end by {
        apply(int32_le_and_not_lt_implies_eq(i, end)) using {
            i <= end;
            not (i < end);
        }
    }
    have forall (k: int32) {
        0 <= k and k < end implies arena->occupied[k] == 1
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < end);
        if k < p {
            have at(before_mark, arena->occupied[k]) == 1 by {
                instantiate(forall (j: int32) {
                    at(before_mark, 0) <= at(before_mark, j) and
                        at(before_mark, j) < at(before_mark, p) implies
                        at(before_mark, arena->occupied[j]) ==
                            at(before_mark, 1)
                }, k) using {
                    0 <= k;
                    k < p;
                }
                assumption();
            }
            have k < start by {
                rewrite(start == p);
                assumption();
            }
            transport(
                at(before_mark, arena->occupied[k]) == 1,
                arena->occupied[k] == 1
            ) using {
                at(before_mark, arena->occupied[k]) == 1;
                0 <= k;
                k < start;
            }
        } else {
            have start <= k by {
                rewrite(start == p);
                arithmetic() using { not (k < p); }
            }
            have k < i by {
                rewrite(i == end);
                assumption();
            }
            instantiate(forall (j: int32) {
                start <= j and j < i implies
                    arena->occupied[j] == 1
            }, k) using {
                start <= k;
                k < i;
            }
            assumption();
        }
    }
    have forall (k: int32) {
        end <= k and k < arena->capacity implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(end <= k);
        extract(k < arena->capacity);
        have p <= k by {
            have p <= end by {
                rewrite(end == p + count);
                arithmetic() using {
                    0 <= p;
                    p <= arena->capacity;
                    arena->capacity <= 536870911;
                    0 < count;
                    count <= arena->capacity;
                }
            }
            apply(int32_le_transitive(p, end, k)) using {
                p <= end;
                end <= k;
            }
        }
        have at(before_mark, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                at(before_mark, p) <= at(before_mark, j) and
                    at(before_mark, j) <
                        at(before_mark, arena->capacity) implies
                    at(before_mark, arena->occupied[j]) ==
                        at(before_mark, 0)
            }, k) using {
                p <= k;
                k < arena->capacity;
            }
            assumption();
        }
        transport(
            at(before_mark, arena->occupied[k]) == 0,
            arena->occupied[k] == 0
        ) using {
            at(before_mark, arena->occupied[k]) == 0;
            end <= k;
            k < arena->capacity;
        }
    }
    have 0 <= end by {
        rewrite(end == p + count);
        arithmetic() using {
            0 <= p;
            p <= arena->capacity;
            arena->capacity <= 536870911;
            0 < count;
            count <= arena->capacity;
        }
    }
    let partition = fold(arena_prefix_partition(
        arena->data,
        arena->occupied,
        arena->capacity
    ), {
        prefix: end
    });
    have p < end by {
        rewrite(end == p + count);
        arithmetic() using {
            0 <= p;
            p <= arena->capacity;
            arena->capacity <= 536870911;
            0 < count;
            count <= arena->capacity;
        }
    }
    have n < end by {
        arithmetic() using {
            n <= p;
            p < end;
        }
    }
    have n + 1 <= end by {
        apply(int32_increment_upper_bound(n, end)) using {
            n < end;
        }
    }
    step();
    have region->arena == arena by {
        normalize();
    }
    step();
    have region->start == p by {
        simp() using {
            start == p;
        }
    }
    step();
    have region->end == p + count by {
        simp() using {
            end == p + count;
        }
    }
    have region->end == region->start + count by {
        normalize();
    }
    have arena->live_regions == n by {
        assumption();
    }
    step();
    have arena->live_regions == n + 1 by {
        simp();
    }
    have defined(p + count) by {
        simp();
    }
    have n <= arena->capacity by {
        apply(int32_le_transitive(n, p, arena->capacity)) using {
            n <= p;
            p <= arena->capacity;
        }
    }
    have n < 2147483647 by {
        arithmetic() using {
            n <= arena->capacity;
            arena->capacity <= 536870911;
        }
    }
    have defined(n + 1) by {
        apply(int32_increment_below_max_is_defined(n)) using {
            n < 2147483647;
        }
    }
    step();
    have result == 1 by {
        normalize();
    }
    let allocated = fold(arena_prefix_region(region), {
        start: p, end: p + count
    });
    let state = fold(arena_prefix_state(arena), {
        prefix: p + count, live: n + 1
    }, { partition: partition });
    let outcome = fold(arena_prefix_alloc_result(arena, region), {
        model: ArenaPrefixAllocOutcome::Success(p + count, n + 1, p, p + count)
    }, { state: state, allocated: allocated });
    have result == 0 or result == 1 by {
        right();
    }
    have result == 0 implies outcome.model ==
        ArenaPrefixAllocOutcome::Failure(p, n) by {
        intro();
        contradiction(result == 0);
    }
    have result == 1 implies outcome.model ==
        ArenaPrefixAllocOutcome::Success(p + count, n + 1, p, p + count) by {
        intro();
        assumption();
    }
    have result == 1 implies region->arena == arena by {
        intro();
        assumption();
    }
    have result == 1 implies region->start == p by {
        intro();
        assumption();
    }
    have result == 1 implies region->end == region->start + count by {
        intro();
        assumption();
    }
    have result == 1 implies arena->live_regions == n + 1 by {
        intro();
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

verifying "arena_free.c";

void arena_free(struct region* region) {
    consumes freed: arena_prefix_region(region);
    consumes before: arena_prefix_state(region->arena);
    requires freed.end == before.prefix;
    requires 1 <= before.live;
    requires before.live - 1 <= freed.start;
    produces object(region);
    produces after: arena_prefix_state(region->arena);

    ensures region->arena == old(region->arena);
    ensures after.prefix == old(freed.start);
    ensures after.live == old(before.live) - 1;
} by {
    let { partition: partition, prefix: p, live: n } = unfold(before);
    let { start: s, end: e } = unfold(freed);
    unfold(partition);
    step();
    step();
    step();
    step();
    mark before_clear;
    loop as clear_occupied {
        decreases region->end - i;
        invariant region->start <= i and i <= region->end;
        invariant forall (k: int32) {
            region->start <= k and k < i implies arena->occupied[k] == 0
        };
        owns arena->occupied[region->start..region->end];
        initialize by {
            have region->start < region->end by {
                simp() using {
                    region->start == s;
                    region->end == e;
                    s < e;
                }
            }
            have i == region->start by {
                simp();
            }
            have region->start <= i and i <= region->end by {
                simp();
            }
            have forall (k: int32) {
                region->start <= k and k < i implies
                    arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(region->start <= k);
                extract(k < i);
                have not (k < i) by {
                    rewrite(i == region->start);
                    arithmetic() using { region->start <= k; }
                }
                contradiction(k < i);
            }
        }
        preserve by {
            mark iteration;
            have region->start == s by {
                assumption();
            }
            have region->end == e by {
                assumption();
            }
            have i + 1 <= region->end by {
                apply(int32_increment_upper_bound(i, region->end)) using {
                    i < region->end;
                }
            }
            have region->start <= i + 1 by {
                apply(int32_increment_lower_bound(
                    i,
                    region->start,
                    region->end
                )) using {
                    region->start <= i;
                    i < region->end;
                }
            }
            have 0 <= region->start by {
                rewrite(region->start == s);
                assumption();
            }
            have 0 <= i by {
                apply(int32_le_transitive(0, region->start, i)) using {
                    0 <= region->start;
                    region->start <= i;
                }
            }
            have 0 <= region->end by {
                arithmetic() using {
                    0 <= i;
                    i < region->end;
                }
            }
            step();
            step();
            have 0 <= 0 - at(iteration, i) + region->end - 1 by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    0 <= region->end;
                    at(iteration, i) < region->end;
                }
            }
            have 0 - at(iteration, i) + region->end - 1
                < 0 - at(iteration, i) + region->end by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    0 <= region->end;
                    at(iteration, i) < region->end;
                }
            }
            have i == at(iteration, i) + 1 by {
                normalize();
            }
            have region->start <= i and i <= region->end by {
                rewrite(i == at(iteration, i) + 1);
                split();
            }
            have forall (k: int32) {
                region->start <= k and k < i implies
                    arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(region->start <= k);
                extract(k < i);
                if k < at(iteration, i) {
                    have k != at(iteration, i) by {
                        apply(int32_lt_implies_neq(
                            k,
                            at(iteration, i)
                        )) using {
                            k < at(iteration, i);
                        }
                    }
                    have at(iteration, arena->occupied[k]) == 0 by {
                        instantiate(forall (j: int32) {
                            at(iteration, region->start) <=
                                at(iteration, j) and
                                at(iteration, j) < at(iteration, i) implies
                                at(iteration, arena->occupied[j]) ==
                                    at(iteration, 0)
                        }, k) using {
                            region->start <= k;
                            k < at(iteration, i);
                        }
                        assumption();
                    }
                    transport(
                        at(iteration, arena->occupied[k]) == 0,
                        arena->occupied[k] == 0
                    ) using {
                        at(iteration, arena->occupied[k]) == 0;
                        region->start <= k;
                        k < at(iteration, i);
                        k != at(iteration, i);
                    }
                } else {
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
                    normalize();
                }
            }
            have region->end <= arena->capacity by {
                simp();
            }
            have arena->capacity <= 536870911 by {
                simp();
            }
            have 0 <= region->start by {
                simp();
            }
            close_invariants by {
                both {
                    intro();
                    intro();
                    simp();
                } and {
                    both {
                        intro();
                        intro();
                        instantiate(forall (k: int32) {
                            region->start <= k and k < i implies
                                arena->occupied[k] == 0
                        }, __click_q0) using {
                            region->start <= __click_q0 and __click_q0 < i;
                        }
                        transport(
                            arena->occupied[__click_q0] == 0,
                            viewable((load_int32_pointer(
                                byte_offset(arena, 8)
                            ) + __click_q0)[0..1])
                        ) using {
                            arena->occupied[__click_q0] == 0;
                            region->start <= __click_q0 and __click_q0 < i;
                            region->start <= i and i <= region->end;
                            0 <= region->start;
                            region->end <= arena->capacity;
                            arena->capacity <= 536870911;
                        }
                    } and {
                        both {
                            intro();
                            intro();
                            assumption();
                        } and {
                            both {
                                assumption();
                            } and {
                                assumption();
                            }
                        }
                    }
                }
            }
        }
    }
    have region->start == s by {
        assumption();
    }
    have region->end == e by {
        assumption();
    }
    have i == region->end by {
        apply(int32_le_and_not_lt_implies_eq(i, region->end)) using {
            i <= region->end;
            not (i < region->end);
        }
    }
    have s <= p by {
        simp();
    }
    have forall (k: int32) {
        0 <= k and k < s implies arena->occupied[k] == 1
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < s);
        have k < p by {
            apply(int32_lt_le_transitive(k, s, p)) using {
                k < s;
                s <= p;
            }
        }
        have at(before_clear, arena->occupied[k]) == 1 by {
            instantiate(forall (j: int32) {
                at(before_clear, 0) <= at(before_clear, j) and
                    at(before_clear, j) < at(before_clear, p) implies
                    at(before_clear, arena->occupied[j]) ==
                        at(before_clear, 1)
            }, k) using {
                0 <= k;
                k < p;
            }
            assumption();
        }
        have k < region->start by {
            rewrite(region->start == s);
            assumption();
        }
        transport(
            at(before_clear, arena->occupied[k]) == 1,
            arena->occupied[k] == 1
        ) using {
            at(before_clear, arena->occupied[k]) == 1;
            0 <= k;
            k < region->start;
        }
    }
    have forall (k: int32) {
        s <= k and k < arena->capacity implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(s <= k);
        extract(k < arena->capacity);
        if k < e {
            have region->start <= k by {
                rewrite(region->start == s);
                assumption();
            }
            have k < i by {
                rewrite(i == region->end);
                rewrite(region->end == e);
                assumption();
            }
            instantiate(forall (j: int32) {
                region->start <= j and j < i implies
                    arena->occupied[j] == 0
            }, k) using {
                region->start <= k;
                k < i;
            }
            assumption();
        } else {
            have e <= k by {
                arithmetic() using { not (k < e); }
            }
            have e == p by {
                assumption();
            }
            have p <= k by {
                simp() using {
                    e <= k;
                    e == p;
                }
            }
            have at(before_clear, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) {
                    at(before_clear, p) <= at(before_clear, j) and
                        at(before_clear, j) <
                            at(before_clear, arena->capacity) implies
                        at(before_clear, arena->occupied[j]) ==
                            at(before_clear, 0)
                }, k) using {
                    p <= k;
                    k < arena->capacity;
                }
                assumption();
            }
            have region->end <= k by {
                simp() using {
                    e <= k;
                    region->end == e;
                    i == region->end;
                }
            }
            have 0 <= region->start by {
                simp();
            }
            have region->start <= region->end by {
                simp();
            }
            have arena->capacity <= 536870911 by {
                simp();
            }
            transport(
                at(before_clear, arena->occupied[k]) == 0,
                arena->occupied[k] == 0
            ) using {
                at(before_clear, arena->occupied[k]) == 0;
                region->end <= k;
                k < arena->capacity;
                arena->capacity <= 536870911;
                0 <= region->start;
                region->start <= region->end;
            }
        }
    }
    let partition = fold(arena_prefix_partition(
        arena->data,
        arena->occupied,
        arena->capacity
    ), {
        prefix: s
    });
    step();
    let after = fold(arena_prefix_state(arena), {
        prefix: s, live: n - 1
    }, { partition: partition });
    execute();
    simp();
}

verifying "arena_write.c";

void arena_write(struct region* region, int32 index, int32 value) {
    owns r: arena_prefix_region(region);
    owns st: arena_prefix_state(region->arena);
    requires 0 <= index;
    requires defined(r.start + index) and r.start + index < r.end;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures st.prefix == old(st.prefix);
    ensures st.live == old(st.live);
    ensures region->arena == old(region->arena);
    ensures region->arena->data[region->start + index] == value;
} by {
    let { partition: partition, prefix: p, live: n } = unfold(st);
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
    let r = fold(arena_prefix_region(region), { start: s, end: e });
    let st = fold(arena_prefix_state(region->arena), {
        prefix: p, live: n
    }, { partition: partition });
    simp();
}

verifying "arena_read.c";

int32 arena_read(struct region* region, int32 index) {
    owns r: arena_prefix_region(region);
    owns st: arena_prefix_state(region->arena);
    requires 0 <= index;
    requires defined(r.start + index) and r.start + index < r.end;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures st.prefix == old(st.prefix);
    ensures st.live == old(st.live);
    ensures region->arena == old(region->arena);
    ensures result == region->arena->data[region->start + index];
} by {
    let { partition: partition, prefix: p, live: n } = unfold(st);
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
    let r = fold(arena_prefix_region(region), { start: s, end: e });
    let st = fold(arena_prefix_state(region->arena), {
        prefix: p, live: n
    }, { partition: partition });
    simp();
}
