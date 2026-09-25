import "arena_resources.click";

spec enum ArenaPrefixAllocOutcome {
    Failure(int32, int32),
    Success(int32, int32, int32, int32),
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

verifying "arena_init.c";

int32 arena_init(struct arena* arena, int32 capacity) {
    consumes object(arena);
    produces arena_init_result(arena, result);
    produces arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        result
    );

    ensures result == 0 or result == 1;
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
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            simp();
        }
        else {}
    }
    branch {
        then {
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            simp();
        }
        else {}
    }
    step();
    branch {
        then {
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            simp();
        }
        else {}
    }
    step();
    branch {
        then {
            step();
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
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
    fold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        result
    ));
    fold(arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        result
    ));
    fold(arena_init_result(arena, result));
    assumption();
    assumption();
    assumption();
    assumption();
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

verifying "arena_destroy.c";

void arena_destroy(struct arena* arena) {
    consumes arena_empty(arena);
    produces object(arena);

    ensures arena->data == 0;
    ensures arena->occupied == 0;
    ensures arena->capacity == 0;
    ensures arena->live_regions == 0;
} by {
    unfold(arena_empty(arena));
    unfold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    unfold(arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    execute();
    simp();
}

verifying "arena_pipeline.c";

int32 arena_pipeline(
    struct arena* arena,
    struct region* first,
    struct region* second,
    struct region* combined
) {
    owns object(arena);
    owns object(first);
    owns object(second);
    owns object(combined);

    ensures result == 0 or result == 33;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    branch {
        then {
            unfold(arena_init_result(arena, initialized));
            unfold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                initialized
            ));
            step();
            have result == 0 by {
                normalize();
            }
            have result == 0 or result == 33 by {
                left();
            }
            simp();
        }
        else {}
    }
    have initialized == 1 by {
        cases(initialized == 0 or initialized == 1) {
            contradiction(initialized == 0);
        } {
            assumption();
        }
    }
    unfold(arena_init_result(arena, initialized));
    unfold(arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        initialized
    ));
    unfold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        initialized
    ));
    have 0 <= arena->capacity by {
        simp();
    }
    have arena->capacity <= 536870911 by {
        simp();
    }
    have arena->live_regions == 0 by {
        simp();
    }
    have arena->capacity <= 1073741823 by {
        arithmetic() using { arena->capacity <= 536870911; }
    }
    have separate(
        memory(object(arena)),
        memory(arena->data[0..arena->capacity])
    ) by {
        both {
            split();
        } and {
            assumption();
        }
    }
    have separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    ) by {
        both {
            split();
        } and {
            assumption();
        }
    }
    fold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    have forall (k: int32) {
        0 <= k and k < 0 implies arena->occupied[k] == 1
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
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    } by {
        simp();
    }
    let partition = fold(arena_prefix_partition(
        arena->data,
        arena->occupied,
        arena->capacity
    ), {
        prefix: 0
    });
    let s0 = fold(arena_prefix_state(arena), {
        prefix: 0, live: 0
    }, { partition: partition });
    let { outcome: o1 } = step(arena_alloc(arena, 2, first), { before: s0 });
    branch {
        then {
            have o1.model == ArenaPrefixAllocOutcome::Failure(0, 0) by {
                simp();
            }
            let { state: f1 } = unfold(o1);
            let { partition: partition_f1, prefix: prefix_f1, live: live_f1 } =
                unfold(f1);
            unfold(partition_f1);
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                1
            ));
            fold(arena_empty(arena));
            step();
            step();
            have result == 0 by {
                normalize();
            }
            have result == 0 or result == 33 by {
                left();
            }
            simp();
        }
        else {}
    }
    have allocated == 1 by {
        cases(allocated == 0 or allocated == 1) {
            contradiction(allocated == 0);
        } {
            assumption();
        }
    }
    have o1.model == ArenaPrefixAllocOutcome::Success(2, 1, 0, 2) by {
        simp();
    }
    let { state: s1, allocated: r1 } = unfold(o1);
    have first->arena == arena by {
        simp();
    }
    let { outcome: o2 } = step(arena_alloc(arena, 2, second), { before: s1 });
    branch {
        then {
            have o2.model == ArenaPrefixAllocOutcome::Failure(2, 1) by {
                simp();
            }
            let { state: f2 } = unfold(o2);
            have first->arena == arena by {
                simp();
            }
            have r1.start == 0 by {
                simp();
            }
            have r1.end == f2.prefix by {
                simp();
            }
            have 1 <= f2.live by {
                simp();
            }
            have f2.live - 1 <= r1.start by {
                simp();
            }
            let { after: g2 } = step(arena_free(first), { freed: r1, before: f2 });
            have g2.prefix == 0 by {
                simp();
            }
            have g2.live == 0 by {
                simp();
            }
            let { partition: partition_g2, prefix: prefix_g2, live: live_g2 } =
                unfold(g2);
            unfold(partition_g2);
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                1
            ));
            fold(arena_empty(arena));
            step();
            step();
            have result == 0 by {
                normalize();
            }
            have result == 0 or result == 33 by {
                left();
            }
            simp();
        }
        else {}
    }
    have allocated == 1 by {
        cases(allocated == 0 or allocated == 1) {
            contradiction(allocated == 0);
        } {
            assumption();
        }
    }
    have o2.model == ArenaPrefixAllocOutcome::Success(4, 2, 2, 4) by {
        simp();
    }
    let { state: s2, allocated: r2 } = unfold(o2);
    have r1.start == 0 by {
        simp();
    }
    have r1.end == 2 by {
        simp();
    }
    have r2.start == 2 by {
        simp();
    }
    have r2.end == 4 by {
        simp();
    }
    have s2.prefix == 4 by {
        simp();
    }
    have s2.live == 2 by {
        simp();
    }
    have first->arena == arena by {
        simp();
    }
    have second->arena == arena by {
        simp();
    }
    mark w1;
    step(arena_write(first, 0, 11), { r: r1, st: s2 });
    have r1.start == at(w1, r1.start) by {
        simp();
    }
    have r1.start == 0 by {
        simp();
    }
    have r1.end == at(w1, r1.end) by {
        simp();
    }
    have r1.end == 2 by {
        simp();
    }
    have s2.prefix == at(w1, s2.prefix) by {
        simp();
    }
    have s2.prefix == 4 by {
        simp();
    }
    have s2.live == at(w1, s2.live) by {
        simp();
    }
    have s2.live == 2 by {
        simp();
    }
    have first->arena->data[first->start + 0] == 11 by {
        simp();
    }
    mark w2;
    step(arena_write(second, 0, 22), { r: r2, st: s2 });
    have r2.start == at(w2, r2.start) by {
        simp();
    }
    have r2.start == 2 by {
        simp();
    }
    have r2.end == at(w2, r2.end) by {
        simp();
    }
    have r2.end == 4 by {
        simp();
    }
    have s2.prefix == at(w2, s2.prefix) by {
        simp();
    }
    have s2.prefix == 4 by {
        simp();
    }
    have s2.live == at(w2, s2.live) by {
        simp();
    }
    have s2.live == 2 by {
        simp();
    }
    have first->arena->data[first->start + 0] == 11 by {
        simp();
    }
    have second->arena->data[second->start + 0] == 22 by {
        simp();
    }
    have r1.start == 0 by {
        simp();
    }
    have r1.end == 2 by {
        simp();
    }
    mark rd1;
    step(arena_read(first, 0), { r: r1, st: s2 });
    have r1.start == at(rd1, r1.start) by {
        simp();
    }
    have r1.start == 0 by {
        simp();
    }
    have r1.end == at(rd1, r1.end) by {
        simp();
    }
    have r1.end == 2 by {
        simp();
    }
    have s2.prefix == at(rd1, s2.prefix) by {
        simp();
    }
    have s2.prefix == 4 by {
        simp();
    }
    have s2.live == at(rd1, s2.live) by {
        simp();
    }
    have s2.live == 2 by {
        simp();
    }
    have second->arena->data[second->start + 0] == 22 by {
        simp();
    }
    have r2.start == 2 by {
        simp();
    }
    have r2.end == 4 by {
        simp();
    }
    mark rd2;
    step(arena_read(second, 0), { r: r2, st: s2 });
    have r2.start == at(rd2, r2.start) by {
        simp();
    }
    have r2.start == 2 by {
        simp();
    }
    have r2.end == at(rd2, r2.end) by {
        simp();
    }
    have r2.end == 4 by {
        simp();
    }
    have s2.prefix == at(rd2, s2.prefix) by {
        simp();
    }
    have s2.prefix == 4 by {
        simp();
    }
    have s2.live == at(rd2, s2.live) by {
        simp();
    }
    have s2.live == 2 by {
        simp();
    }
    have first_value == 11 by {
        simp();
    }
    have second_value == 22 by {
        simp();
    }
    step();
    have value == 33 by {
        simp() using {
            value == first_value + second_value;
            first_value == 11;
            second_value == 22;
        }
    }
    have second->arena == arena by {
        simp();
    }
    have r2.end == s2.prefix by {
        simp();
    }
    have 1 <= s2.live by {
        simp();
    }
    have s2.live - 1 <= r2.start by {
        simp();
    }
    mark f2;
    let { after: s3 } = step(arena_free(second), { freed: r2, before: s2 });
    have s3.prefix == at(f2, r2.start) by {
        simp();
    }
    have at(f2, r2.start) == 2 by {
        simp();
    }
    have s3.prefix == 2 by {
        simp() using {
            s3.prefix == at(f2, r2.start);
            at(f2, r2.start) == 2;
        }
    }
    have s3.live == at(f2, s2.live) - 1 by {
        simp();
    }
    have at(f2, s2.live) == 2 by {
        simp();
    }
    have s3.live == 1 by {
        simp() using {
            s3.live == at(f2, s2.live) - 1;
            at(f2, s2.live) == 2;
        }
    }
    have first->arena == arena by {
        simp();
    }
    have r1.start == 0 by {
        simp();
    }
    have r1.end == 2 by {
        simp();
    }
    have r1.end == s3.prefix by {
        simp();
    }
    have 1 <= s3.live by {
        simp();
    }
    have s3.live - 1 <= r1.start by {
        simp();
    }
    mark f1;
    let { after: s4 } = step(arena_free(first), { freed: r1, before: s3 });
    have s4.prefix == at(f1, r1.start) by {
        simp();
    }
    have at(f1, r1.start) == 0 by {
        simp();
    }
    have s4.prefix == 0 by {
        simp() using {
            s4.prefix == at(f1, r1.start);
            at(f1, r1.start) == 0;
        }
    }
    have s4.live == at(f1, s3.live) - 1 by {
        simp();
    }
    have at(f1, s3.live) == 1 by {
        simp();
    }
    have s4.live == 0 by {
        simp() using {
            s4.live == at(f1, s3.live) - 1;
            at(f1, s3.live) == 1;
        }
    }
    have value == 33 by {
        simp();
    }
    mark a3;
    let { outcome: o3 } = step(arena_alloc(arena, 4, combined), { before: s4 });
    have at(a3, s4.prefix) == 0 by {
        simp();
    }
    have at(a3, s4.live) == 0 by {
        simp();
    }
    branch {
        then {
            have o3.model == ArenaPrefixAllocOutcome::Failure(
                at(a3, s4.prefix),
                at(a3, s4.live)
            ) by {
                simp();
            }
            let { state: f3 } = unfold(o3);
            have f3.prefix == 0 by {
                simp() using {
                    f3.prefix == at(a3, s4.prefix);
                    at(a3, s4.prefix) == 0;
                }
            }
            have f3.live == 0 by {
                simp() using {
                    f3.live == at(a3, s4.live);
                    at(a3, s4.live) == 0;
                }
            }
            let { partition: partition_f3, prefix: prefix_f3, live: live_f3 } =
                unfold(f3);
            unfold(partition_f3);
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                1
            ));
            fold(arena_empty(arena));
            step();
            step();
            have result == 0 by {
                normalize();
            }
            have result == 0 or result == 33 by {
                left();
            }
            simp();
        }
        else {}
    }
    have allocated == 1 by {
        cases(allocated == 0 or allocated == 1) {
            contradiction(allocated == 0);
        } {
            assumption();
        }
    }
    have o3.model == ArenaPrefixAllocOutcome::Success(
        at(a3, s4.prefix) + 4,
        at(a3, s4.live) + 1,
        at(a3, s4.prefix),
        at(a3, s4.prefix) + 4
    ) by {
        simp();
    }
    let { state: s5, allocated: r3 } = unfold(o3);
    have r3.start == 0 by {
        simp() using {
            r3.start == at(a3, s4.prefix);
            at(a3, s4.prefix) == 0;
        }
    }
    have r3.end == 4 by {
        simp() using {
            r3.end == at(a3, s4.prefix) + 4;
            at(a3, s4.prefix) == 0;
        }
    }
    have s5.prefix == 4 by {
        simp() using {
            s5.prefix == at(a3, s4.prefix) + 4;
            at(a3, s4.prefix) == 0;
        }
    }
    have s5.live == 1 by {
        simp() using {
            s5.live == at(a3, s4.live) + 1;
            at(a3, s4.live) == 0;
        }
    }
    have combined->arena == arena by {
        simp();
    }
    have value == 33 by {
        simp();
    }
    have combined->start == at(a3, s4.prefix) by {
        extract(combined->start == at(a3, s4.prefix));
    }
    have combined->start == 0 by {
        simp() using {
            combined->start == at(a3, s4.prefix);
            at(a3, s4.prefix) == 0;
        }
    }
    let { partition: q5, prefix: p5, live: n5 } = unfold(s5);
    let { start: c0, end: c1 } = unfold(r3);
    have defined(combined->start + 3) by {
        rewrite(combined->start == 0);
        normalize();
    }
    let r3 = fold(arena_prefix_region(combined), { start: c0, end: c1 });
    let s5 = fold(arena_prefix_state(arena), {
        prefix: p5, live: n5
    }, { partition: q5 });
    mark w3;
    step(arena_write(combined, 3, value), { r: r3, st: s5 });
    have r3.start == at(w3, r3.start) by {
        simp();
    }
    have at(w3, r3.start) == 0 by {
        simp();
    }
    have r3.start == 0 by {
        simp() using {
            r3.start == at(w3, r3.start);
            at(w3, r3.start) == 0;
        }
    }
    have r3.end == at(w3, r3.end) by {
        simp();
    }
    have at(w3, r3.end) == 4 by {
        simp();
    }
    have r3.end == 4 by {
        simp() using {
            r3.end == at(w3, r3.end);
            at(w3, r3.end) == 4;
        }
    }
    have s5.prefix == at(w3, s5.prefix) by {
        simp();
    }
    have at(w3, s5.prefix) == 4 by {
        simp();
    }
    have s5.prefix == 4 by {
        simp() using {
            s5.prefix == at(w3, s5.prefix);
            at(w3, s5.prefix) == 4;
        }
    }
    have s5.live == at(w3, s5.live) by {
        simp();
    }
    have at(w3, s5.live) == 1 by {
        simp();
    }
    have s5.live == 1 by {
        simp() using {
            s5.live == at(w3, s5.live);
            at(w3, s5.live) == 1;
        }
    }
    have combined->start == 0 by {
        simp();
    }
    have defined(combined->start + 3) by {
        rewrite(combined->start == 0);
        normalize();
    }
    have combined->arena->data[combined->start + 3] == value by {
        simp();
    }
    have value == 33 by {
        simp();
    }
    have combined->arena->data[combined->start + 3] == 33 by {
        simp() using {
            combined->arena->data[combined->start + 3] == value;
            value == 33;
        }
    }
    mark r3m;
    step(arena_read(combined, 3), { r: r3, st: s5 });
    have value == combined->arena->data[combined->start + 3] by {
        simp();
    }
    have combined->arena->data[combined->start + 3] == 33 by {
        simp();
    }
    have r3.start == at(r3m, r3.start) by {
        simp();
    }
    have at(r3m, r3.start) == 0 by {
        simp();
    }
    have r3.start == 0 by {
        simp() using {
            r3.start == at(r3m, r3.start);
            at(r3m, r3.start) == 0;
        }
    }
    have r3.end == at(r3m, r3.end) by {
        simp();
    }
    have at(r3m, r3.end) == 4 by {
        simp();
    }
    have r3.end == 4 by {
        simp() using {
            r3.end == at(r3m, r3.end);
            at(r3m, r3.end) == 4;
        }
    }
    have s5.prefix == at(r3m, s5.prefix) by {
        simp();
    }
    have at(r3m, s5.prefix) == 4 by {
        simp();
    }
    have s5.prefix == 4 by {
        simp() using {
            s5.prefix == at(r3m, s5.prefix);
            at(r3m, s5.prefix) == 4;
        }
    }
    have s5.live == at(r3m, s5.live) by {
        simp();
    }
    have at(r3m, s5.live) == 1 by {
        simp();
    }
    have s5.live == 1 by {
        simp() using {
            s5.live == at(r3m, s5.live);
            at(r3m, s5.live) == 1;
        }
    }
    have value == 33 by {
        simp() using {
            value == combined->arena->data[combined->start + 3];
            combined->arena->data[combined->start + 3] == 33;
        }
    }
    have r3.end == s5.prefix by {
        simp() using {
            r3.end == 4;
            s5.prefix == 4;
        }
    }
    have 1 <= s5.live by {
        simp() using { s5.live == 1; }
    }
    have s5.live - 1 <= r3.start by {
        simp() using {
            s5.live == 1;
            r3.start == 0;
        }
    }
    mark f3;
    let { after: s6 } = step(arena_free(combined), { freed: r3, before: s5 });
    have s6.prefix == at(f3, r3.start) by {
        simp();
    }
    have at(f3, r3.start) == 0 by {
        simp();
    }
    have s6.prefix == 0 by {
        simp() using {
            s6.prefix == at(f3, r3.start);
            at(f3, r3.start) == 0;
        }
    }
    have s6.live == at(f3, s5.live) - 1 by {
        simp();
    }
    have at(f3, s5.live) == 1 by {
        simp();
    }
    have s6.live == 0 by {
        simp() using {
            s6.live == at(f3, s5.live) - 1;
            at(f3, s5.live) == 1;
        }
    }
    let { partition: partition_s6, prefix: prefix_s6, live: live_s6 } =
        unfold(s6);
    unfold(partition_s6);
    fold(arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    fold(arena_empty(arena));
    step();
    step();
    have result == 33 by {
        simp();
    }
    have result == 0 or result == 33 by {
        right();
    }
    simp();
}
