import click::separation;

theorem selected_array_cell(whole: Resource, kept: Resource, p: int32*, len: int32, i: int32) {
    requires separate(whole, memory(p[0..len]));
    requires contains(whole, kept);
    requires 0 <= i;
    requires i < len;
    ensures separate(kept, memory(p[i])) by {
        have i <= 2147483646 by { close() using { i < len; }; }
        have defined(i + 1) by { close() using { 0 <= i; i <= 2147483646; }; }
        have i <= ((i + 1) as int32) by { close() using { 0 <= i; i < len; }; }
        have ((i + 1) as int32) <= len by { close() using { 0 <= i; i < len; }; }
        have contains(memory(p[0..len]), memory(p[i..i + 1])) by {
            apply(separation::contains_subrange(p, 0, len, i, i + 1));
        }
        have separate(kept, memory(p[i..i + 1])) by {
            apply(separation::separate_restrict(whole, memory(p[0..len]), kept, memory(p[i..i + 1])));
        }
        have contains(kept, kept) by { apply(separation::contains_refl(kept)); }
        have contains(memory(p[i..i + 1]), memory(p[i])) by { normalize(); }
        apply(separation::separate_restrict(kept, memory(p[i..i + 1]), kept, memory(p[i])));
    }
}

import click::integer;

resource preserved_cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}

resource arena_initialized_storage(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    initialized: int32
) {
    if initialized == 1 {
        owns allocation(data, capacity * 4);
        owns allocation(occupied, capacity * 4);
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
    owns *arena;
    owns arena_initialized_storage(
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
        memory(*arena),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    );
}

resource arena_region(region: struct region*) {
    field start: int32;
    field end: int32;
    owns *region;
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
            owns *arena;
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
    consumes *arena;
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
        true => {
            step();
            let outcome = fold(arena_init_outcome(arena), {
                model: ArenaInitOutcome::Failure
            });
            close();
        }
        false => {}
    }
    branch {
        true => {
            step();
            let outcome = fold(arena_init_outcome(arena), {
                model: ArenaInitOutcome::Failure
            });
            close();
        }
        false => {}
    }
    step();
    branch {
        true => {
            step();
            let outcome = fold(arena_init_outcome(arena), {
                model: ArenaInitOutcome::Failure
            });
            close();
        }
        false => {}
    }
    step();
    branch {
        true => {
            step();
            step();
            let outcome = fold(arena_init_outcome(arena), {
                model: ArenaInitOutcome::Failure
            });
            close();
        }
        false => {}
    }
    have 1 <= capacity;
    have separate(memory(occupied[0..capacity]), memory(data[0..capacity])) by { close(); }
    have separate(memory(*arena), memory(data[0..capacity])) by { close(); }
    step();
    have separate(memory(occupied[0..capacity]), memory(*arena)) by { close(); }
    have contains(memory(*arena), memory(arena->live_regions)) by { normalize(); }
    mark initialize_entry;
    have arena->live_regions == 0;
    loop initialize_occupied {
        decreases to_integer(capacity) - to_integer(i);
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 0
        };
        owns occupied[0..capacity];

        initialize by close();
        maintain by {
            mark iteration;
            step();
            step();
            have to_integer(at(iteration, i) + 1) == to_integer(at(iteration, i)) + 1;
            have 0 <= to_integer(capacity) - to_integer(at(iteration, i) + 1);
            have forall (k: int32) { 0 <= k and k < i implies occupied[k] == 0 } by {
                intro(); intro();
                have 0 <= k;
                have k < i;
                if k < at(iteration, i) {
                    have at(iteration, occupied[k]) == 0 by {
                        have at(iteration, 0) <= at(iteration, k) and at(iteration, k) < at(iteration, i);
                        instantiate(forall (j: int32) {
                            at(iteration, 0) <= at(iteration, j) and at(iteration, j) < at(iteration, i) implies
                                at(iteration, occupied[j]) == at(iteration, 0)
                        }, k);
                        close();
                    }
                    have at(iteration, i) != k by { close() using { k < at(iteration, i); }; }
                    have at(iteration, separate(memory(occupied[i]), memory(occupied[k]))) by {
                        apply(separation::separate_elements(occupied, at(iteration, i), k));
                    }
                    have separate(loop(0).statement(0).footprint, memory(occupied[k])) by {
                        close() using { at(iteration, separate(memory(occupied[i]), memory(occupied[k]))); };
                    }
                    have at(loop(0).statement(0).exit, occupied[k]) == at(iteration, occupied[k]) by {
                        preserve(memory(occupied[k]), loop(0).statement(0));
                    }
                    have separate(loop(0).statement(1).footprint, memory(occupied[k])) by { close() using {}; }
                    have occupied[k] == at(loop(0).statement(1).entry, occupied[k]) by {
                        preserve(memory(occupied[k]), loop(0).statement(1));
                    }
                    close();
                } else {
                    have k == at(iteration, i) by { close(); }
                    rewrite(k, at(iteration, i));
                    close();
                }
            }
            close();
        }
    }
    have at(initialize_entry, arena->live_regions) == 0;
    have contains(memory(occupied[0..capacity]), memory(occupied[0..capacity])) by {
        apply(separation::contains_refl(memory(occupied[0..capacity])));
    }
    have separate(memory(occupied[0..capacity]), memory(arena->live_regions)) by {
        apply(separation::separate_restrict(memory(occupied[0..capacity]), memory(*arena), memory(occupied[0..capacity]), memory(arena->live_regions)));
    }
    have separate(initialize_occupied.footprint, memory(arena->live_regions)) by {
        close() using { separate(memory(occupied[0..capacity]), memory(arena->live_regions)); };
    }
    have arena->live_regions == at(initialize_entry, arena->live_regions) by {
        preserve(memory(arena->live_regions), initialize_occupied);
    }
    have arena->live_regions == 0 by { close(); }
    have i == capacity;
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 0
    } by {
        intro();
        intro();
        have 0 <= k;
        have k < capacity;
        have 0 <= k and k < i;
        instantiate(forall (j: int32) {
            0 <= j and j < i implies occupied[j] == 0
        }, k);
        close();
    }
    step();
    step();
    step();
    have arena->occupied == occupied;
    have arena->data == data by { close(); }
    have arena->capacity == capacity;
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        instantiate(forall (j: int32) {
            0 <= j and j < capacity implies occupied[j] == 0
        }, k);
        have occupied[k] == 0 by { close(); }
        rewrite(arena->occupied, occupied);
        close();
    }
    fold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    have arena->capacity <= 1073741823;
    have separate(
        memory(arena->occupied[0..arena->capacity]),
        memory(arena->data[0..arena->capacity])
    ) by {
        rewrite(arena->occupied, occupied);
        rewrite(arena->data, data);
        rewrite(arena->capacity, capacity);
        close();
    }
    have separate(
        memory(*arena),
        memory(arena->data[0..arena->capacity])
    ) by {
        rewrite(arena->data, data);
        rewrite(arena->capacity, capacity);
        close();
    }
    have separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    ) by {
        rewrite(arena->occupied, occupied);
        rewrite(arena->capacity, capacity);
        close();
    }
    fold(arena_cells(arena->data, arena->occupied, arena->capacity)[..]);
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    let state = fold(arena_state(arena), { live: 0, capacity: arena->capacity });
    step();
    have forall (k: int32) {
        result == 1 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        have result == 1;
        have 0 <= k;
        have k < arena->capacity;
        instantiate(forall (j: int32) {
            0 <= j and j < arena->capacity implies arena->occupied[j] == 0
        }, k);
        close();
    }
    let outcome = fold(arena_init_outcome(arena), {
        model: ArenaInitOutcome::Success(0, capacity),
        state: state
    });
    close();
}


spec enum ArenaAllocOutcome {
    Failure,
    Success(int32, int32),
}

resource arena_alloc_result(region: struct region*) {
    field model: ArenaAllocOutcome;
    match model {
        ArenaAllocOutcome::Failure => {
            owns *region;
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
    consumes *region;
    produces outcome: arena_alloc_result(region);
    requires st.live < 2147483647;

    ensures forall (k: int32) {
        result == 0 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == old(arena->occupied[k])
    };
    ensures result == 0 or result == 1;
    ensures st.live == old(st.live) + result;
    ensures arena->capacity == old(arena->capacity);
    ensures arena->capacity <= 536870911;
    ensures st.capacity == arena->capacity;
    ensures result == 0 implies outcome.model == ArenaAllocOutcome::Failure;
    ensures result == 1 implies outcome.model ==
        ArenaAllocOutcome::Success(region->start, region->end);
    ensures result == 1 implies region->arena == arena;
    ensures result == 1 implies region->end == region->start + count;
    ensures result == 1 implies region->end <= arena->capacity;
    ensures result == 1 implies 0 <= region->start;
    ensures result == 1 implies region->start < region->end;
    ensures forall (k: int32) {
        result == 1 and region->start <= k and k < region->end implies
            arena->occupied[k] == 1
    };
    ensures forall (k: int32) {
        result == 1 and 0 <= k and k < region->start implies
            arena->occupied[k] == old(arena->occupied[k])
    };
    ensures forall (k: int32) {
        result == 1 and region->end <= k and k < arena->capacity implies
            arena->occupied[k] == old(arena->occupied[k])
    };
    ensures forall (k: int32) {
        result == 1 and region->start <= k and k < region->end implies
            old(arena->occupied[k]) == 0
    };
} by {
    let { live: n } = unfold(st);
    step();
    step();
    step();
    step();
    if at(region(4).entry, count) <= at(region(4).entry, 0) {
        step();
        step();
        let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), { model: ArenaAllocOutcome::Failure() });
        have result == 0 by {
            close();
        }
        have forall (k: int32) { result == 0 and 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            close();
        }
        close();
        have result == 0 or result == 1 by {
            close();
        }
        close();
        have to_integer(st.live) == (to_integer(old(st.live)) + to_integer(result)) by {
            close();
        }
        close();
        have arena->capacity == old(arena->capacity) by {
            close();
        }
        close();
        have arena->capacity <= 536870911 by {
            close();
        }
        close();
        have st.capacity == arena->capacity by {
            close();
        }
        close();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure() by {
            intro();
            close();
        }
        close();
        have result == 1 implies outcome.model == ArenaAllocOutcome::Success(region->start, region->end) by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies region->arena == arena by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies to_integer(region->end) == (to_integer(region->start) + to_integer(count)) by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies region->end <= arena->capacity by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies 0 <= region->start by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies region->start < region->end by {
            intro();
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and 0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        close();
        close();
    } else {
        step();
        step();
    }
    if at(region(7).entry, count) > at(region(7).entry, arena->capacity) {
        step();
        step();
        let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), { model: ArenaAllocOutcome::Failure() });
        have result == 0 by {
            close();
        }
        have forall (k: int32) { result == 0 and 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            close();
        }
        close();
        have result == 0 or result == 1 by {
            close();
        }
        close();
        have to_integer(st.live) == (to_integer(old(st.live)) + to_integer(result)) by {
            close();
        }
        close();
        have arena->capacity == old(arena->capacity) by {
            close();
        }
        close();
        have arena->capacity <= 536870911 by {
            close();
        }
        close();
        have st.capacity == arena->capacity by {
            close();
        }
        close();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure() by {
            intro();
            close();
        }
        close();
        have result == 1 implies outcome.model == ArenaAllocOutcome::Success(region->start, region->end) by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies region->arena == arena by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies to_integer(region->end) == (to_integer(region->start) + to_integer(count)) by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies region->end <= arena->capacity by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies 0 <= region->start by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies region->start < region->end by {
            intro();
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and 0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        close();
        close();
    } else {
        step();
        step();
    }
    have 0 < count by {
        close();
    }
    have count <= arena->capacity by {
        close();
    }
    unfold(arena_cells(arena->data, arena->occupied, arena->capacity));
    step();
    step();
    have 0 <= arena->capacity by {
        have 0 <= count by { apply(integer::int32_less_than_implies_less_equal(0, count)); }
        apply(integer::int32_less_equal_transitive(0, count, arena->capacity));
    }
    have forall (k: int32) { 0 <= k and k < 0 implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have 0 <= k;
        have k < 0;
        have not k < 0 by {
            close();
        }
        contradiction(k < 0);
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        close();
    }
    have viewable(arena->occupied[0..arena->capacity]) by {
        observe(old(arena->occupied)[0..old(arena->capacity)]);
    }
    let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), { lo: 0, hi: 0 });
    loop find_first_free_run {
        decreases (to_integer(arena->capacity) - to_integer(i));
        owns run: arena_scan(arena->data, arena->occupied, arena->capacity);
        invariant run.hi == i;
        invariant (to_integer(run.lo) + to_integer(run_length)) == to_integer(i);
        invariant 0 <= run_length and run_length <= count;
        invariant forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) };
        invariant arena->data == old(arena->data);
        invariant arena->occupied == old(arena->occupied);
        initialize by {
            have run.hi == i by {
                close();
            }
            have (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) by {
                close();
            }
            have 0 <= run_length and run_length <= count by {
                all {
                    0 <= run_length => {
                        close();
                    }
                    run_length <= count => {
                        close() using { at(function.entry, 0) < at(function.entry, count); };
                    }
                }
            }
            have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } by {
                close();
            }
            have arena->data == old(arena->data) by {
                close();
            }
            have arena->occupied == old(arena->occupied) by {
                close();
            }
        }
        maintain by {
            mark iteration;
            let { lo: lo, hi: hi } = unfold(run);
            have hi == i by {
                close();
            }
            have (to_integer(lo) + to_integer(run_length)) == to_integer(i) by {
                close();
            }
            have lo <= i by {
                close();
            }
            have 0 <= i by {
                close() using { 0 <= lo; at(function.entry, lo) <= at(function.entry, i); };
            }
            have (to_integer(i) + 1) <= to_integer(arena->capacity) by {
                close() using { to_integer(i) < to_integer(arena->capacity); };
            }
            if arena->occupied[i] == 0 {
                have (to_integer(run_length) + 1) <= to_integer(count) by {
                    close() using { to_integer(run_length) < to_integer(count); };
                }
                if at(region(13).entry, arena->occupied[i]) == at(region(13).entry, 0) {
                    step();
                    step();
                } else {
                }
                step();
                have forall (k: int32) { lo <= k and k < i implies arena->occupied[k] == 0 } by {
                    intro();
                    intro();
                    have lo <= k;
                    have k < i;
                    if k < at(iteration, i) {
                        have k < hi by {
                            close();
                        }
                        instantiate(forall (j: int32) { lo <= j and j < hi implies arena->occupied[j] == 0 }, k);
                        close();
                    } else {
                        have k <= at(iteration, i) by {
                            close() using { (at(region(13).entry, i) as int32) <
                                    (at(region(13).entry, arena->capacity) as int32); (k as int32) < (i as int32); (0 as int32) <= (at(region(13).entry, i) as int32); (at(function.entry, arena->capacity) as int32) <=
                                    (at(function.entry, 536870911) as int32); };
                        }
                        have k == at(iteration, i) by {
                            close() using { k <= at(iteration, i); not k < at(region(13).entry, i); };
                        }
                        rewrite(k, at(iteration, i));
                        close();
                    }
                }
                have to_integer(at(iteration, i)) < (to_integer(at(iteration, i)) + 1) by {
                    close();
                }
                have at(iteration, i) < i by {
                    close() using { (at(region(13).entry, i) as int32) < (at(region(13).entry,
                            arena->capacity) as int32); };
                }
                have at(iteration, i) <= i by {
                    apply(integer::int32_less_than_implies_less_equal(at(iteration, i), i));
                }
                have lo <= i by {
                    close() using { lo <= at(region(13).entry, i); at(iteration, i) < i; };
                }
                have i <= arena->capacity by {
                    close() using { (at(region(13).entry, i) as int32) < (at(region(13).entry,
                            arena->capacity) as int32); };
                }
                have to_integer(run_length) == (to_integer(at(iteration, run_length)) + 1) by {
                    have -2147483648 <= (to_integer(at(iteration, run_length)) + 1) by {
                        close() using { 0 <= to_integer(at(iteration, run_length)); };
                    }
                    have (to_integer(at(iteration, run_length)) + 1) <= 2147483647 by {
                        close() using { (let integer_value: Integer = to_integer(at(region(13).entry,
                                (i as int32))) + 1; integer_value) <= to_integer(at(region(0).entry,
                                (arena->capacity as int32))); (let integer_value: Integer = to_integer((lo as int32)) +
                                to_integer(at(region(13).entry, (run_length as int32)));
                                integer_value) == to_integer(at(region(13).entry, (i as int32))); 0 <= to_integer((lo as int32)); to_integer(at(region(0).entry, (arena->capacity as int32)))
                                <= 536870911; };
                    }
                    have to_integer(run_length) == (to_integer(at(iteration, run_length)) + 1) by {
                        close() using { -2147483648 <= (to_integer(at(iteration, run_length)) + 1); (to_integer(at(iteration, run_length)) + 1) <= 2147483647; };
                    }
                    close();
                }
                have (to_integer(lo) + to_integer(at(iteration, run_length))) == to_integer(at(iteration, i)) by {
                    close();
                }
                have (to_integer(lo) + to_integer(run_length)) == to_integer(i) by {
                    have (to_integer(lo) + to_integer(run_length)) <= to_integer(i) by {
                        close() using { (to_integer(lo) + to_integer(at(iteration, run_length))) ==
                                to_integer(at(iteration, i)); to_integer(run_length) == (to_integer(at(iteration,
                                run_length)) + 1); to_integer(at(iteration, i)) < to_integer(i); };
                    }
                    have to_integer(i) <= (to_integer(lo) + to_integer(run_length)) by {
                        have -2147483648 <= (to_integer(at(iteration, run_length)) + 1) by {
                            close() using { 0 <= to_integer(at(iteration, run_length)); };
                        }
                        have (to_integer(at(iteration, run_length)) + 1) <= 2147483647 by {
                            close() using { (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value) <= to_integer(at(region(0).entry,
                                    (arena->capacity as int32))); (to_integer(lo) + to_integer(at(iteration, run_length)))
                                    == to_integer(at(iteration, i)); 0 <= to_integer(lo); to_integer(at(region(0).entry, (arena->capacity as
                                    int32))) <= 536870911; };
                        }
                        have to_integer(run_length) == (to_integer(at(iteration, run_length)) + 1) by {
                            close() using { -2147483648 <= (to_integer(at(iteration, run_length)) +
                                    1); (to_integer(at(iteration, run_length)) + 1) <= 2147483647; };
                        }
                        have -2147483648 <= (to_integer(at(iteration, i)) + 1) by {
                            close() using { 0 <= to_integer(at(iteration, i)); };
                        }
                        have (to_integer(at(iteration, i)) + 1) <= 2147483647 by {
                            close() using { (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value) <= to_integer(at(region(0).entry,
                                    (arena->capacity as int32))); to_integer(at(region(0).entry, (arena->capacity as
                                    int32))) <= 536870911; };
                        }
                        have to_integer(i) == (to_integer(at(iteration, i)) + 1) by {
                            close() using { -2147483648 <= (to_integer(at(iteration, i)) + 1); (to_integer(at(iteration, i)) + 1) <= 2147483647; };
                        }
                        close() using { (to_integer(lo) + to_integer(at(iteration, run_length))) ==
                                to_integer(at(iteration, i)); to_integer(i) == (to_integer(at(iteration, i)) + 1); to_integer(run_length) == (to_integer(at(iteration,
                                run_length)) + 1); };
                    }
                    close() using { (to_integer(lo) + to_integer(run_length)) <= to_integer(i); to_integer(i) <= (to_integer(lo) + to_integer(run_length)); };
                }
                have 0 <= run_length and run_length <= count by {
                    all {
                        0 <= run_length => {
                            close() using { (at(region(13).entry, 0) as int32) <= (at(region(13).entry,
                                    run_length) as int32); (at(region(13).entry, run_length) as int32) <
                                    (at(region(13).entry, count) as int32); };
                        }
                        run_length <= count => {
                            close();
                        }
                    }
                }
                have viewable(arena->occupied[0..arena->capacity]) by {
                    observe(at(find_first_free_run.entry, arena->occupied)[0..at(find_first_free_run.entry, arena->capacity)]);
                }
                let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), { lo: lo, hi: i });
                have run.hi == i by {
                    close();
                }
                have (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) by {
                    close();
                }
                have 0 <= at(iteration, i) by {
                    close();
                }
                have to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration, i)) + 1) by {
                    have -2147483648 <= (to_integer(at(iteration, i)) + 1) by {
                        close() using { 0 <= to_integer(at(iteration, i)); };
                    }
                    have (to_integer(at(iteration, i)) + 1) <= 2147483647 by {
                        close() using { (let integer_value: Integer = to_integer(at(region(13).entry,
                                (i as int32))) + 1; integer_value) <= to_integer(at(region(0).entry,
                                (arena->capacity as int32))); to_integer(at(region(0).entry, (arena->capacity as int32)))
                                <= 536870911; };
                    }
                    have to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration, i)) + 1) by {
                        close() using { -2147483648 <= (to_integer(at(iteration, i)) + 1); (to_integer(at(iteration, i)) + 1) <= 2147483647; };
                    }
                    close();
                }
                have 0 <= (to_integer(arena->capacity) - to_integer((at(iteration, i) + 1))) by {
                    close() using { (let integer_value: Integer = to_integer(at(region(13).entry, (i
                            as int32))) + 1; integer_value) <= to_integer(at(region(0).entry,
                            (arena->capacity as int32))); to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration,
                            i)) + 1); };
                }
                have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    have 0 <= k;
                    have k < arena->capacity;
                    have at(iteration, arena->occupied[k]) == at(find_first_free_run.entry, arena->occupied[k]) by {
                        have at(iteration, 0) <= at(iteration, k) and at(iteration, k) < at(iteration, arena->capacity);
                        instantiate(forall (j: int32) { at(iteration, 0) <= at(iteration, j) and at(iteration, j) < at(iteration, arena->capacity) implies at(iteration, arena->occupied[j]) == at(find_first_free_run.entry, arena->occupied[j]) }, k);
                        close();
                    }
                    close();
                }
                have arena->data == old(arena->data) by {
                    close();
                }
                have arena->occupied == old(arena->occupied) by {
                    close();
                }
                have (to_integer(arena->capacity) - to_integer(i)) < at(region(13).entry, (to_integer(arena->capacity) - to_integer(i))) by {
                    rewrite(to_integer((at(iteration, i) + 1)), (to_integer(at(iteration, i)) + 1));
                    close();
                }
            } else {
                if at(region(13).entry, arena->occupied[i]) == at(region(13).entry, 0) {
                } else {
                    step();
                    step();
                }
                step();
                have forall (k: int32) { i <= k and k < i implies arena->occupied[k] == 0 } by {
                    intro();
                    intro();
                    have i <= k;
                    have k < i;
                    have not k < i by {
                        close();
                    }
                    contradiction(k < i);
                }
                have 0 <= i by {
                    close() using { (0 as int32) <= (at(region(13).entry, i) as int32); (at(region(13).entry, i) as int32) < (at(region(13).entry,
                            arena->capacity) as int32); };
                }
                have i <= arena->capacity by {
                    close() using { (at(region(13).entry, i) as int32) < (at(region(13).entry,
                            arena->capacity) as int32); };
                }
                have viewable(arena->occupied[0..arena->capacity]) by {
                    observe(at(find_first_free_run.entry, arena->occupied)[0..at(find_first_free_run.entry, arena->capacity)]);
                }
                let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), { lo: i, hi: i });
                have 0 <= at(iteration, i) by {
                    close();
                }
                have to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration, i)) + 1) by {
                    have -2147483648 <= (to_integer(at(iteration, i)) + 1) by {
                        close() using { 0 <= to_integer(at(iteration, i)); };
                    }
                    have (to_integer(at(iteration, i)) + 1) <= 2147483647 by {
                        close() using { (let integer_value: Integer = to_integer(at(region(13).entry,
                                (i as int32))) + 1; integer_value) <= to_integer(at(region(0).entry,
                                (arena->capacity as int32))); to_integer(at(region(0).entry, (arena->capacity as int32)))
                                <= 536870911; };
                    }
                    have to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration, i)) + 1) by {
                        close() using { -2147483648 <= (to_integer(at(iteration, i)) + 1); (to_integer(at(iteration, i)) + 1) <= 2147483647; };
                    }
                    close();
                }
                have 0 <= (to_integer(arena->capacity) - to_integer((at(iteration, i) + 1))) by {
                    close() using { (let integer_value: Integer = to_integer(at(region(13).entry, (i
                            as int32))) + 1; integer_value) <= to_integer(at(region(0).entry,
                            (arena->capacity as int32))); to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration,
                            i)) + 1); };
                }
                have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    have 0 <= k;
                    have k < arena->capacity;
                    have at(iteration, arena->occupied[k]) == at(find_first_free_run.entry, arena->occupied[k]) by {
                        have at(iteration, 0) <= at(iteration, k) and at(iteration, k) < at(iteration, arena->capacity);
                        instantiate(forall (j: int32) { at(iteration, 0) <= at(iteration, j) and at(iteration, j) < at(iteration, arena->capacity) implies at(iteration, arena->occupied[j]) == at(find_first_free_run.entry, arena->occupied[j]) }, k);
                        close();
                    }
                    close();
                }
                have run.hi == i by {
                    close();
                }
                have run.hi == i implies (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) by {
                    intro();
                    close();
                }
                have run.hi == i implies (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) implies 0 <= run_length and run_length <= count by {
                    intro();
                    intro();
                    all {
                        0 <= run_length => {
                            close();
                        }
                        run_length <= count => {
                            close() using { at(function.entry, 0) < at(function.entry, count); };
                        }
                    }
                }
                have run.hi == i implies (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) implies 0 <= run_length and run_length <= count implies forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    intro();
                    close();
                }
                have run.hi == i implies (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) implies 0 <= run_length and run_length <= count implies forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } implies arena->data == old(arena->data) by {
                    intro();
                    intro();
                    intro();
                    intro();
                    close();
                }
                have run.hi == i implies (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) implies 0 <= run_length and run_length <= count implies forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } implies arena->data == old(arena->data) implies arena->occupied == old(arena->occupied) by {
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    close();
                }
                have (to_integer(arena->capacity) - to_integer(i)) < at(region(13).entry, (to_integer(arena->capacity) - to_integer(i))) by {
                    rewrite(to_integer((at(iteration, i) + 1)), (to_integer(at(iteration, i)) + 1));
                    close();
                }
            }
        }
    }
    let { lo: run_lo, hi: run_hi } = unfold(run);
    have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        have arena->occupied[k] == old(arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < arena->capacity implies arena->occupied[j] == at(find_first_free_run.entry, arena->occupied[j]) }, k);
            close();
        }
        have at(find_first_free_run.entry, 0) <= at(find_first_free_run.entry, k) and at(find_first_free_run.entry, k) < at(find_first_free_run.entry, arena->capacity);
        instantiate(forall (j: int32) { at(find_first_free_run.entry, 0) <= at(find_first_free_run.entry, j) and at(find_first_free_run.entry, j) < at(find_first_free_run.entry, arena->capacity) implies at(find_first_free_run.entry, arena->occupied[j]) == old(arena->occupied[j]) }, k);
        rewrite(arena->occupied[k], at(find_first_free_run.entry, arena->occupied[k]));
        close();
    }
    mark scanned;
    if at(region(17).entry, run_length) < at(region(17).entry, count) {
        step();
        fold(arena_cells(arena->data, arena->occupied, arena->capacity));
        step();
        let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), { model: ArenaAllocOutcome::Failure() });
        have result == 0 by {
            close();
        }
        have forall (k: int32) { result == 0 and 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            have arena->occupied[k] == old(arena->occupied[k]) by {
                have at(scanned, 0) <= at(scanned, k) and at(scanned, k) < at(scanned, arena->capacity);
                instantiate(forall (j: int32) { at(scanned, 0) <= at(scanned, j) and at(scanned, j) < at(scanned, arena->capacity) implies at(scanned, arena->occupied[j]) == old(arena->occupied[j]) }, k);
                close();
            }
            close();
        }
        close();
        have result == 0 or result == 1 by {
            close();
        }
        close();
        have to_integer(st.live) == (to_integer(old(st.live)) + to_integer(result)) by {
            close();
        }
        close();
        have arena->capacity == old(arena->capacity) by {
            close();
        }
        close();
        have arena->capacity <= 536870911 by {
            close();
        }
        close();
        have st.capacity == arena->capacity by {
            close();
        }
        close();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure() by {
            intro();
            close();
        }
        close();
        have result == 1 implies outcome.model == ArenaAllocOutcome::Success(region->start, region->end) by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies region->arena == arena by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies to_integer(region->end) == (to_integer(region->start) + to_integer(count)) by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies region->end <= arena->capacity by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies 0 <= region->start by {
            intro();
            contradiction(result == 1);
        }
        close();
        have result == 1 implies region->start < region->end by {
            intro();
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and 0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            have result == 1;
            have not result == 1 by {
                close();
            }
            contradiction(result == 1);
        }
        close();
        close();
        close();
    } else {
        step();
        step();
        have run_length == count by {
            have at(loop(0).exit, run_length) <= at(loop(0).exit, count);
            close() using { at(loop(0).exit, run_length) <= at(loop(0).exit, count); not run_length < count; };
        }
        have count == run_length by {
            close();
        }
        have (to_integer(run_lo) + to_integer(count)) == to_integer(i) by {
            close();
        }
        have 0 <= count by {
            close();
        }
        have defined((run_lo + count)) by {
            have (to_integer(run_lo) + to_integer(count)) >= -2147483648 by {
                close() using { 0 < to_integer(count); 0 <= to_integer(run_lo); };
            }
            have (to_integer(run_lo) + to_integer(count)) <= 2147483647 by {
                close() using { to_integer(count) <= to_integer(at(region(7).entry, arena->capacity)); to_integer(run_lo) <= to_integer(run_hi); to_integer(run_hi) <= to_integer(at(region(7).entry,
                        arena->capacity)); to_integer(at(region(7).entry, arena->capacity)) <= 536870911; };
            }
            close();
        }
        have to_integer(count) <= (to_integer(run_lo) + to_integer(count)) by {
            close() using { 0 <= to_integer(run_lo); };
        }
        have to_integer(i) == (to_integer(run_lo) + to_integer(count)) by {
            close();
        }
        have count <= i by {
            close();
        }
        have defined((i - count)) by {
            have at(loop(0).exit, 0) <= at(loop(0).exit, run_length);
            have at(loop(0).exit, run_length) <= at(loop(0).exit, count);
            have at(function.entry, arena->capacity) <= at(function.entry, 1073741823);
            have (let integer_value: Integer = to_integer((run_lo as int32)) + to_integer((count as int32)); integer_value) <= 2147483647;
            have (let integer_value: Integer = to_integer((run_lo as int32)) + to_integer((count as int32)); integer_value) >= -2147483648;
            have to_integer(at(function.entry, i)) <= 2147483647 by {
                close() using {  };
            }
            have -2147483648 <= (to_integer(at(function.entry, i)) - to_integer(at(function.entry, count))) by {
                close() using { at(function.entry, count) <= at(function.entry, i); };
            }
            have (to_integer(at(function.entry, i)) - to_integer(at(function.entry, count))) <= 2147483647 by {
                close() using { at(function.entry, 0) <= at(function.entry, count); to_integer(at(function.entry, i)) <= 2147483647; };
            }
            close();
        }
        step();
        have to_integer((i - count)) == (to_integer(i) - to_integer(count)) by {
            have -2147483648 <= (to_integer(i) - to_integer(count)) by {
                close();
            }
            have (to_integer(i) - to_integer(count)) <= 2147483647 by {
                close();
            }
            have to_integer((i - count)) == (to_integer(i) - to_integer(count)) by {
                close() using { -2147483648 <= (to_integer(i) - to_integer(count)); (to_integer(i) - to_integer(count)) <= 2147483647; };
            }
            close();
        }
        have to_integer(i) - to_integer(count) == to_integer(run_lo) by {
            rewrite(to_integer(i), to_integer(run_lo) + to_integer(count));
            close();
        }
        have to_integer(start) == to_integer(run_lo) by {
            rewrite(to_integer(i - count), to_integer(i) - to_integer(count));
            close();
        }
        have start == run_lo by {
            close();
        }
        step();
        have end == i by {
            close();
        }
        have run_lo <= arena->capacity by {
            apply(integer::int32_less_equal_transitive(run_lo, run_hi, arena->capacity));
        }
        have start < end by {
            close() using { (at(function.entry, 0) as int32) < (at(function.entry, count) as int32); (at(function.entry, count) as int32) <= (at(function.entry, i) as int32); (at(region(7).entry, count) as int32) <= (at(region(7).entry,
                    arena->capacity) as int32); (at(function.entry, arena->capacity) as int32) <= (at(function.entry,
                    536870911) as int32); };
        }
        have forall (k: int32) { start <= k and k < end implies arena->occupied[k] == 0 } by {
            rewrite(start, run_lo);
            rewrite(end, i);
            rewrite(at(loop(0).exit, i), at(loop(0).exit, run.hi));
            close();
        }
        step();
        have i == start by {
            close();
        }
        have 0 <= start by {
            close();
        }
        have start <= end by {
            close();
        }
        have end <= arena->capacity by {
            close();
        }
        have forall (k: int32) { start <= k and k < start implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            have start <= k;
            have k < start;
            have not k < start by {
                close();
            }
            contradiction(k < start);
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            have arena->occupied[k] == old(arena->occupied[k]) by {
                have at(scanned, 0) <= at(scanned, k) and at(scanned, k) < at(scanned, arena->capacity);
                instantiate(forall (j: int32) { at(scanned, 0) <= at(scanned, j) and at(scanned, j) < at(scanned, arena->capacity) implies at(scanned, arena->occupied[j]) == old(arena->occupied[j]) }, k);
                close();
            }
            close();
        }
        have forall (k: int32) { start <= k and k < end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            have start <= k;
            have k < end;
            have 0 <= start by { close(); }
            have 0 <= k by {
                apply(click::integer::int32_less_equal_transitive(0, start, k));
            }
            have k < arena->capacity by {
                apply(integer::int32_less_than_less_equal_transitive(k, end, arena->capacity));
            }
            have old(arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { start <= j and j < end implies arena->occupied[j] == 0 }, k);
                close();
            }
            instantiate(forall (j: int32) { 0 <= j and j < arena->capacity implies arena->occupied[j] == old(arena->occupied[j]) }, k);
            close();
        }
        have viewable(arena->occupied[0..arena->capacity]) by {
            observe(old(arena->occupied)[0..old(arena->capacity)]);
        }
        let w = fold(arena_window(arena->data, arena->occupied, arena->capacity, start, end), { next: start });
        loop mark_free_run {
            decreases (to_integer(end) - to_integer(i));
            owns w: arena_window(arena->data, arena->occupied, arena->capacity, start, end);
            invariant w.next == i;
            invariant forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) };
            invariant forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) };
            invariant arena->data == old(arena->data);
            invariant arena->occupied == old(arena->occupied);
            initialize by {
                have w.next == i by {
                    close();
                }
                have forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    close();
                }
                have forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    close();
                }
                have arena->data == old(arena->data) by {
                    close();
                }
                have arena->occupied == old(arena->occupied) by {
                    close();
                }
            }
            maintain by {
                let { next: m } = unfold(w);
                have m == i by {
                    close();
                }
                have m <= i by {
                    close() using { end == end; (at(region(24).entry, w.next) as int32) == (at(region(24).entry,
                            i) as int32); };
                }
                have i < end by {
                    close();
                }
                have end <= arena->capacity by {
                    close();
                }
                have arena->occupied[i] == 0 by {
                    instantiate(forall (k: int32) { m <= k and k < end implies arena->occupied[k] == 0 }, i);
                    close();
                }
                unfold(arena_window(arena->data, arena->occupied, arena->capacity, start, end)[i]);
                have start <= i by {
                    close();
                }
                have 0 <= start by { close(); }
                have 0 <= i by {
                    apply(click::integer::int32_less_equal_transitive(0, start, i));
                }
                have i < arena->capacity by {
                    apply(integer::int32_less_than_less_equal_transitive(i, end, arena->capacity));
                }
                mark opened;
                have contains(memory(*arena), memory(arena->occupied)) by {
                    close();
                }
                have separate(memory(arena->occupied), memory(arena->occupied[i])) by {
                    apply(selected_array_cell(memory(*arena), memory(arena->occupied), arena->occupied, arena->capacity, i));
                }
                have contains(memory(*arena), memory(arena->data)) by {
                    close();
                }
                have separate(memory(arena->data), memory(arena->occupied[i])) by {
                    apply(selected_array_cell(memory(*arena), memory(arena->data), arena->occupied, arena->capacity, i));
                }
                have separate(memory(arena->occupied), memory(old(arena->occupied)[i])) by {
                    rewrite(old(arena->occupied), arena->occupied);
                    close();
                }
                have separate(memory(arena->data), memory(old(arena->occupied)[i])) by {
                    rewrite(old(arena->occupied), arena->occupied);
                    close();
                }
                have contains(memory(*arena), memory(arena->capacity)) by { close(); }
                have separate(memory(arena->capacity), memory(arena->occupied[i])) by {
                    apply(selected_array_cell(memory(*arena), memory(arena->capacity), arena->occupied, arena->capacity, i));
                }
                step();
                have separate(statement(13).statement(0).footprint, memory(arena->occupied)) by {
                    close();
                }
                have arena->occupied == at(opened, arena->occupied) by {
                    preserve(memory(arena->occupied), statement(13).statement(0));
                }
                have arena->occupied == old(arena->occupied) by {
                    close();
                }
                have at(opened, separate(statement(13).statement(0).footprint, memory(arena->capacity))) by {
                    close();
                }
                have arena->capacity == at(opened, arena->capacity) by {
                    preserve(at(opened, memory(arena->capacity)), statement(13).statement(0));
                }
                have arena->capacity == old(arena->capacity) by { close(); }
                have separate(statement(13).statement(0).footprint, memory(arena->data)) by {
                    close();
                }
                have arena->data == at(opened, arena->data) by {
                    preserve(memory(arena->data), statement(13).statement(0));
                }
                have arena->data == old(arena->data) by {
                    close();
                }
                have forall (k: int32) { (to_integer(at(opened, i)) + 1) <= to_integer(k) and k < end implies arena->occupied[k] == 0 } by {
                    intro();
                    intro();
                    have (to_integer(at(opened, i)) + 1) <= to_integer(k);
                    have k < end;
                    have at(opened, i) < k by {
                        close() using { (let integer_value: Integer = to_integer((i as int32)) + 1;
                                integer_value) <= to_integer((k as int32)); };
                    }
                    have at(opened, i) <= k by {
                        apply(integer::int32_less_than_implies_less_equal(at(opened, i), k));
                    }
                    have m <= k by {
                        close();
                    }
                    have at(opened, arena->occupied[k]) == 0 by {
                        have at(opened, m) <= at(opened, k) and at(opened, k) < at(opened, end);
                        instantiate(forall (j: int32) { at(opened, m) <= at(opened, j) and at(opened, j) < at(opened, end) implies at(opened, arena->occupied[j]) == at(opened, 0) }, k);
                        close();
                    }
                    have 0 <= k by {
                        close() using { (at(function.entry, 0) as int32) <= (at(function.entry, i) as
                                int32); (at(opened, i) as int32) <= (k as int32); };
                    }
                    have k < at(opened, arena->capacity) by {
                        apply(integer::int32_less_than_less_equal_transitive(k, end, at(opened, arena->capacity)));
                    }
                    have at(opened, i) != k by { close() using { at(opened, i) < k; }; }
                    have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                        apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k));
                    }
                    have separate(statement(13).statement(0).footprint, memory(at(opened, arena->occupied)[k])) by {
                        close();
                    }
                    have at(statement(13).statement(0).exit, (let saved: int32* = at(opened, arena->occupied); saved[k]))
                        == at(statement(13).statement(0).entry, (let saved: int32* = at(opened, arena->occupied); saved[k])) by {
                        preserve(memory(at(opened, arena->occupied)[k]), statement(13).statement(0));
                    }
                    rewrite(arena->occupied, at(opened, arena->occupied));
                    close();
                }
                have forall (k: int32) { start <= k and to_integer(k) < (to_integer(at(opened, i)) + 1) implies arena->occupied[k] == 1 } by {
                    intro();
                    intro();
                    have start <= k;
                    have to_integer(k) < (to_integer(at(opened, i)) + 1);
                    if k < at(opened, i) {
                        have k < m by {
                            close();
                        }
                        have at(opened, arena->occupied[k]) == 1 by {
                            have at(opened, start) <= at(opened, k) and at(opened, k) < at(opened, m);
                            instantiate(forall (j: int32) { at(opened, start) <= at(opened, j) and at(opened, j) < at(opened, m) implies at(opened, arena->occupied[j]) == at(opened, 1) }, k);
                            close();
                        }
                        have 0 <= k by {
                            apply(click::integer::int32_less_equal_transitive(0, start, k));
                        }
                        have at(opened, i) != k by { close() using { k < at(opened, i); }; }
                        have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                            apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k));
                        }
                        have separate(statement(13).statement(0).footprint, memory(at(opened, arena->occupied)[k])) by {
                            close();
                        }
                        have at(statement(13).statement(0).exit, (let saved: int32* = at(opened, arena->occupied); saved[k]))
                            == at(statement(13).statement(0).entry, (let saved: int32* = at(opened, arena->occupied); saved[k])) by {
                            preserve(memory(at(opened, arena->occupied)[k]), statement(13).statement(0));
                        }
                        rewrite(arena->occupied, at(opened, arena->occupied));
                        close();
                    } else {
                        have k <= at(opened, i) by {
                            close() using { (let integer_value: Integer = to_integer((k as int32));
                                    integer_value) < (to_integer((i as int32)) + 1); };
                        }
                        have k == at(opened, i) by {
                            close() using { k <= at(opened, i); not k < i; };
                        }
                        have at(statement(13).statement(0).exit,
                            (let occupied: int32* = old(arena->occupied); occupied[i])) == 1 by { close(); }
                        rewrite(k, at(opened, i));
                        rewrite(arena->occupied, old(arena->occupied));
                        close();
                    }
                }
                step();
                have forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    have 0 <= k;
                    have k < start;
                    have at(opened, arena->occupied[k]) == at(mark_free_run.entry, arena->occupied[k]) by {
                        have at(opened, 0) <= at(opened, k) and at(opened, k) < at(opened, start);
                        instantiate(forall (j: int32) { at(opened, 0) <= at(opened, j) and at(opened, j) < at(opened, start) implies at(opened, arena->occupied[j]) == at(mark_free_run.entry, arena->occupied[j]) }, k);
                        close();
                    }
                    have k < at(opened, i) by {
                        apply(integer::int32_less_than_less_equal_transitive(k, start, at(opened, i)));
                    }
                    have at(opened, i) != k by { close() using { k < at(opened, i); }; }
                    have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                        apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k));
                    }
                    have separate(statement(13).statement(0).footprint, memory(at(opened, arena->occupied)[k])) by {
                        close();
                    }
                    have at(statement(13).statement(0).exit, (let saved: int32* = at(opened, arena->occupied); saved[k]))
                        == at(statement(13).statement(0).entry, (let saved: int32* = at(opened, arena->occupied); saved[k])) by {
                        preserve(memory(at(opened, arena->occupied)[k]), statement(13).statement(0));
                    }
                    rewrite(arena->occupied, at(opened, arena->occupied));
                    close();
                }
                have forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    have end <= k;
                    have k < arena->capacity;
                    have k < at(opened, arena->capacity) by {
                        close();
                    }
                    have at(opened, arena->occupied[k]) == at(mark_free_run.entry, arena->occupied[k]) by {
                        have at(opened, end) <= at(opened, k) and at(opened, k) < at(opened, arena->capacity);
                        instantiate(forall (j: int32) { at(opened, end) <= at(opened, j) and at(opened, j) < at(opened, arena->capacity) implies at(opened, arena->occupied[j]) == at(mark_free_run.entry, arena->occupied[j]) }, k);
                        close();
                    }
                    have at(opened, i) < k by {
                        apply(integer::int32_less_than_less_equal_transitive(at(opened, i), end, k));
                    }
                    have at(opened, i) <= k by {
                        apply(integer::int32_less_than_implies_less_equal(at(opened, i), k));
                    }
                    have 0 <= k by {
                        close() using { (0 as int32) <= (at(region(24).entry, i) as int32); (at(opened, i) as int32) <= (k as int32); };
                    }
                    have at(opened, i) != k by { close() using { at(opened, i) < k; }; }
                    have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                        apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k));
                    }
                    have separate(statement(13).statement(0).footprint, memory(at(opened, arena->occupied)[k])) by {
                        close();
                    }
                    have at(statement(13).statement(0).exit, (let saved: int32* = at(opened, arena->occupied); saved[k]))
                        == at(statement(13).statement(0).entry, (let saved: int32* = at(opened, arena->occupied); saved[k])) by {
                        preserve(memory(at(opened, arena->occupied)[k]), statement(13).statement(0));
                    }
                    rewrite(arena->occupied, at(opened, arena->occupied));
                    close();
                }
                have forall (k: int32) { i <= k and k < end implies arena->occupied[k] == 0 } by {
                    intro();
                    intro();
                    have i <= k;
                    have k < end;
                    have (to_integer(at(opened, i)) + 1) <= to_integer(k) by {
                        have -2147483648 <= (to_integer(at(opened, i)) + 1) by {
                            close() using { 0 <= to_integer(at(opened, i)); };
                        }
                        have (to_integer(at(opened, i)) + 1) <= 2147483647 by {
                            close() using { (let integer_value: Integer = to_integer((run_lo as
                                    int32)) + to_integer((count as int32)); integer_value) <=
                                    2147483647; (let integer_value: Integer = to_integer((end as int32));
                                    integer_value) == (to_integer((run_lo as int32)) +
                                    to_integer((count as int32))); to_integer(at(opened, i)) < to_integer((let
                                    integer_value: Integer = to_integer((end as int32));
                                    integer_value)); };
                        }
                        have to_integer((i as int32)) == (to_integer(at(opened, i)) + 1) by {
                            close() using { -2147483648 <= (to_integer(at(opened, i)) + 1); (to_integer(at(opened, i)) + 1) <= 2147483647; };
                        }
                        rewrite(to_integer(at(opened, i)) + 1, to_integer(i));
                        close();
                    }
                    instantiate(forall (j: int32) { (to_integer(at(opened, i)) + 1) <= to_integer(j) and j < end implies arena->occupied[j] == 0 }, k);
                    close();
                }
                have forall (k: int32) { start <= k and k < i implies arena->occupied[k] == 1 } by {
                    intro();
                    intro();
                    have start <= k;
                    have k < i;
                    have to_integer(k) < (to_integer(at(opened, i)) + 1) by {
                        have -2147483648 <= (to_integer(at(opened, i)) + 1) by {
                            close() using { 0 <= to_integer(at(opened, i)); };
                        }
                        have (to_integer(at(opened, i)) + 1) <= 2147483647 by {
                            close() using { (let integer_value: Integer = to_integer((run_lo as
                                    int32)) + to_integer((count as int32)); integer_value) <=
                                    2147483647; (let integer_value: Integer = to_integer((end as int32));
                                    integer_value) == (to_integer((run_lo as int32)) +
                                    to_integer((count as int32))); to_integer(at(opened, i)) < to_integer((let
                                    integer_value: Integer = to_integer((end as int32));
                                    integer_value)); };
                        }
                        have to_integer((i as int32)) == (to_integer(at(opened, i)) + 1) by {
                            close() using { -2147483648 <= (to_integer(at(opened, i)) + 1); (to_integer(at(opened, i)) + 1) <= 2147483647; };
                        }
                        close() using { to_integer((i as int32)) == (to_integer(at(opened, i)) + 1); to_integer(k) < to_integer((i as int32)); };
                    }
                    instantiate(forall (j: int32) { start <= j and to_integer(j) < (to_integer(at(opened, i)) + 1) implies arena->occupied[j] == 1 }, k);
                    close();
                }
                observe(at(opened, arena->occupied)[0..at(opened, arena->capacity)]);
                have forall (k: int32) { i <= k and k < end implies load<int32>((old(arena->occupied) + k)) == 0 } by {
                    intro();
                    intro();
                    instantiate(forall (j: int32) { i <= j and j < end implies arena->occupied[j] == 0 }, k);
                    have &arena->occupied[k] == old(&arena->occupied[k]) by {
                        close();
                    }
                    close();
                }
                have forall (k: int32) { start <= k and k < i implies load<int32>((old(arena->occupied) + k)) == 1 } by {
                    intro();
                    intro();
                    instantiate(forall (j: int32) { start <= j and j < i implies arena->occupied[j] == 1 }, k);
                    have &arena->occupied[k] == old(&arena->occupied[k]) by {
                        close();
                    }
                    close();
                }
                have to_integer(i) == (to_integer(at(opened, i)) + 1) by {
                    have -2147483648 <= (to_integer(at(opened, i)) + 1) by {
                        close() using { 0 <= to_integer(at(opened, i)); };
                    }
                    have (to_integer(at(opened, i)) + 1) <= 2147483647 by {
                        close() using { (let integer_value: Integer = to_integer((run_lo as int32)) +
                                to_integer((count as int32)); integer_value) <= 2147483647; (let integer_value: Integer = to_integer((end as int32));
                                integer_value) == (to_integer((run_lo as int32)) + to_integer((count
                                as int32))); to_integer(at(opened, i)) < to_integer((let integer_value:
                                Integer = to_integer((end as int32)); integer_value)); };
                    }
                    have to_integer(i) == (to_integer(at(opened, i)) + 1) by {
                        close() using { -2147483648 <= (to_integer(at(opened, i)) + 1); (to_integer(at(opened, i)) + 1) <= 2147483647; };
                    }
                    close();
                }
                have start <= i by {
                    close() using { start <= at(opened, i); to_integer(i) == to_integer(at(opened, i)) + 1; };
                }
                have i <= end by {
                    close() using { at(opened, i) < end; to_integer(i) == to_integer(at(opened, i)) + 1; };
                }
                let w = fold(arena_window(old(arena->data), old(arena->occupied), old(arena->capacity), start, end), { next: i });
                have 0 <= (to_integer(end) - to_integer(i)) by {
                    close() using { to_integer(i) <= to_integer(end); };
                }
                have (to_integer(end) - to_integer(i)) < (to_integer(end) - to_integer(at(opened, i))) by {
                    rewrite(to_integer(i), (to_integer(at(opened, i)) + 1));
                    close();
                }
                have w.next == i by {
                    close();
                }
                have w.next == i implies forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    close();
                }
                have w.next == i implies forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } implies forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    close();
                }
                have w.next == i implies forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } implies forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } implies arena->data == old(arena->data) by {
                    intro();
                    intro();
                    intro();
                    close();
                }
                have w.next == i implies forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } implies forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } implies arena->data == old(arena->data) implies arena->occupied == old(arena->occupied) by {
                    intro();
                    intro();
                    intro();
                    intro();
                    close();
                }
            }
        }
        let { next: m } = unfold(w);
        have m <= end by {
            close();
        }
        have m == i by {
            close();
        }
        have not m < end by {
            close();
        }
        have m == end by {
            close() using { at(function.entry, m) <= at(function.entry, end); not at(function.entry, m) < at(function.entry, end); };
        }
        have forall (k: int32) { start <= k and k < end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            have start <= k;
            have k < end;
            have k < m by {
                close();
            }
            instantiate(forall (j: int32) { start <= j and j < m implies arena->occupied[j] == 1 }, k);
            close();
        }
        have forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have 0 <= k;
            have k < start;
            have arena->occupied[k] == old(arena->occupied[k]) by {
                instantiate(forall (j: int32) { 0 <= j and j < start implies arena->occupied[j] == at(mark_free_run.entry, arena->occupied[j]) }, k);
                close();
            }
            have k < end by {
                close() using { k < start; at(function.entry, start) < at(function.entry, end); };
            }
            have k < arena->capacity by {
                apply(integer::int32_less_than_less_equal_transitive(k, end, arena->capacity));
            }
            have at(mark_free_run.entry, 0) <= at(mark_free_run.entry, k) and at(mark_free_run.entry, k) < at(mark_free_run.entry, arena->capacity);
            instantiate(forall (j: int32) { at(mark_free_run.entry, 0) <= at(mark_free_run.entry, j) and at(mark_free_run.entry, j) < at(mark_free_run.entry, arena->capacity) implies at(mark_free_run.entry, arena->occupied[j]) == old(arena->occupied[j]) }, k);
            close();
        }
        have forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have end <= k;
            have k < arena->capacity;
            have arena->occupied[k] == old(arena->occupied[k]) by {
                instantiate(forall (j: int32) { end <= j and j < arena->capacity implies arena->occupied[j] == at(mark_free_run.entry, arena->occupied[j]) }, k);
                close();
            }
            have 0 <= end by {
                close() using { (at(function.entry, 0) as int32) <= (at(function.entry, count) as
                        int32); (count as int32) <= (end as int32); };
            }
            have 0 <= k by {
                close() using { (at(function.entry, 0) as int32) <= (at(function.entry, end) as
                        int32); (end as int32) <= (k as int32); };
            }
            have at(mark_free_run.entry, 0) <= at(mark_free_run.entry, k) and at(mark_free_run.entry, k) < at(mark_free_run.entry, arena->capacity);
            instantiate(forall (j: int32) { at(mark_free_run.entry, 0) <= at(mark_free_run.entry, j) and at(mark_free_run.entry, j) < at(mark_free_run.entry, arena->capacity) implies at(mark_free_run.entry, arena->occupied[j]) == old(arena->occupied[j]) }, k);
            close();
        }
        mark marked;
        step();
        step();
        step();
        have arena->live_regions == n by {
            close();
        }
        have n < 2147483647 by {
            close();
        }
        have defined((n + 1)) by {
            have at(loop(0).exit, 0) <= at(loop(0).exit, run_length);
            have at(loop(0).exit, run_length) <= at(loop(0).exit, count);
            have at(function.entry, arena->capacity) <= at(function.entry, 1073741823);
            have (let integer_value: Integer = to_integer((run_lo as int32)) + to_integer((count as int32)); integer_value) <= 2147483647;
            have (let integer_value: Integer = (to_integer((end as int32)) - to_integer((count as int32))); integer_value) <= 2147483647;
            have (let integer_value: Integer = to_integer((run_lo as int32)) + to_integer((count as int32)); integer_value) >= -2147483648;
            have (let integer_value: Integer = (to_integer((end as int32)) - to_integer((count as int32))); integer_value) >= -2147483648;
            close() using { at(function.entry, st.live) < at(function.entry, 2147483647); };
        }
        step();
        have region->start == start by {
            close();
        }
        have region->end == end by {
            close();
        }
        have forall (k: int32) { region->start <= k and k < region->end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            have region->start <= k;
            have k < region->end;
            have start <= k by {
                close();
            }
            have k < end by {
                close();
            }
            have 0 <= start by { close(); }
            have 0 <= k by {
                apply(click::integer::int32_less_equal_transitive(0, start, k));
            }
            have k < arena->capacity by {
                apply(integer::int32_less_than_less_equal_transitive(k, end, arena->capacity));
            }
            have at(marked, start) <= at(marked, k) and at(marked, k) < at(marked, end);
            instantiate(forall (j: int32) { at(marked, start) <= at(marked, j) and at(marked, j) < at(marked, end) implies at(marked, arena->occupied[j]) == at(marked, 1) }, k);
            have separate(memory(*region), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*region), memory(region->arena)) by { close(); }
            have separate(memory(region->arena), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*region), memory(region->arena), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(14).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(14).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(14).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(14));
            }
            have separate(memory(*region), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*region), memory(region->start)) by { close(); }
            have separate(memory(region->start), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*region), memory(region->start), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(15).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(15).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(15).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(15));
            }
            have separate(memory(*region), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*region), memory(region->end)) by { close(); }
            have separate(memory(region->end), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*region), memory(region->end), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(16).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(16).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(16).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(16));
            }
            have separate(memory(*arena), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*arena), memory(arena->live_regions)) by { close(); }
            have separate(memory(arena->live_regions), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*arena), memory(arena->live_regions), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(17).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(17).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(17).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(17));
            }
            close();
        }
        have forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have 0 <= k;
            have k < region->start;
            have k < start by {
                close();
            }
            have k < end by {
                close() using { at(function.entry, k) < at(function.entry, start); at(function.entry, start) < at(function.entry, end); };
            }
            have k < arena->capacity by {
                apply(integer::int32_less_than_less_equal_transitive(k, end, arena->capacity));
            }
            have at(marked, 0) <= at(marked, k) and at(marked, k) < at(marked, start);
            instantiate(forall (j: int32) { at(marked, 0) <= at(marked, j) and at(marked, j) < at(marked, start) implies at(marked, arena->occupied[j]) == old(arena->occupied[j]) }, k);
            have separate(memory(*region), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*region), memory(region->arena)) by { close(); }
            have separate(memory(region->arena), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*region), memory(region->arena), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(14).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(14).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(14).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(14));
            }
            have separate(memory(*region), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*region), memory(region->start)) by { close(); }
            have separate(memory(region->start), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*region), memory(region->start), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(15).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(15).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(15).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(15));
            }
            have separate(memory(*region), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*region), memory(region->end)) by { close(); }
            have separate(memory(region->end), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*region), memory(region->end), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(16).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(16).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(16).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(16));
            }
            have separate(memory(*arena), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*arena), memory(arena->live_regions)) by { close(); }
            have separate(memory(arena->live_regions), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*arena), memory(arena->live_regions), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(17).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(17).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(17).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(17));
            }
            close();
        }
        have forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have region->end <= k;
            have k < arena->capacity;
            have end <= k by {
                close();
            }
            have 0 <= end by {
                close() using { (at(function.entry, 0) as int32) <= (at(function.entry, count) as
                        int32); (count as int32) <= (end as int32); };
            }
            have 0 <= k by {
                close() using { (at(function.entry, 0) as int32) <= (at(function.entry, end) as
                        int32); (at(function.entry, end) as int32) <= (at(function.entry, k) as
                        int32); };
            }
            have at(marked, end) <= at(marked, k) and at(marked, k) < at(marked, arena->capacity);
            instantiate(forall (j: int32) { at(marked, end) <= at(marked, j) and at(marked, j) < at(marked, arena->capacity) implies at(marked, arena->occupied[j]) == old(arena->occupied[j]) }, k);
            have separate(memory(*region), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*region), memory(region->arena)) by { close(); }
            have separate(memory(region->arena), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*region), memory(region->arena), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(14).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(14).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(14).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(14));
            }
            have separate(memory(*region), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*region), memory(region->start)) by { close(); }
            have separate(memory(region->start), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*region), memory(region->start), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(15).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(15).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(15).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(15));
            }
            have separate(memory(*region), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*region), memory(region->end)) by { close(); }
            have separate(memory(region->end), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*region), memory(region->end), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(16).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(16).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(16).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(16));
            }
            have separate(memory(*arena), memory(at(marked, arena->occupied)[0..at(marked, arena->capacity)])) by { close(); }
            have contains(memory(*arena), memory(arena->live_regions)) by { close(); }
            have separate(memory(arena->live_regions), memory(at(marked, arena->occupied)[k])) by {
                apply(selected_array_cell(memory(*arena), memory(arena->live_regions), at(marked, arena->occupied), at(marked, arena->capacity), k));
            }
            have separate(statement(17).footprint, memory(at(marked, arena->occupied)[k])) by {
                close();
            }
            have at(statement(17).exit, (let saved: int32* = at(marked, arena->occupied); saved[k])) == at(statement(17).entry, (let saved: int32* = at(marked, arena->occupied); saved[k])) by {
                preserve(memory(at(marked, arena->occupied)[k]), statement(17));
            }
            close();
        }
        mark stored;
        have forall (k: int32) { region->start <= k and k < region->end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            have region->start <= k;
            have k < region->end;
            have start <= k by {
                close();
            }
            have k < end by {
                close();
            }
            instantiate(forall (j: int32) { start <= j and j < end implies old(arena->occupied[j]) == 0 }, k);
            close();
        }
        fold(arena_cells(arena->data, arena->occupied, arena->capacity));
        let allocated = fold(arena_region(region), { start: start, end: end });
        let st = fold(arena_state(arena), { live: (n + 1), capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), { model: ArenaAllocOutcome::Success(start, end), allocated: allocated });
        step();
        have result == 1 by {
            close();
        }
        have forall (k: int32) { result == 0 and 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have result == 0;
            have not result == 0 by {
                close();
            }
            contradiction(result == 0);
        }
        close();
        have result == 0 or result == 1 by {
            close();
        }
        close();
        have to_integer(st.live) == (to_integer(old(st.live)) + to_integer(result)) by {
            have -2147483648 <= (to_integer(old(st.live)) + 1) by {
                close();
            }
            have (to_integer(old(st.live)) + 1) <= 2147483647 by {
                close();
            }
            have to_integer(st.live) == (to_integer(old(st.live)) + 1) by {
                close() using { -2147483648 <= (to_integer(old(st.live)) + 1); (to_integer(old(st.live)) + 1) <= 2147483647; };
            }
            close();
        }
        close();
        have arena->capacity == old(arena->capacity) by {
            close();
        }
        close();
        have arena->capacity <= 536870911 by {
            close();
        }
        close();
        have st.capacity == arena->capacity by {
            close();
        }
        close();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure() by {
            intro();
            contradiction(result == 0);
        }
        close();
        have result == 1 implies outcome.model == ArenaAllocOutcome::Success(region->start, region->end) by {
            intro();
            close();
        }
        close();
        have result == 1 implies region->arena == arena by {
            intro();
            close();
        }
        close();
        have result == 1 implies to_integer(region->end) == (to_integer(region->start) + to_integer(count)) by {
            intro();
            close();
        }
        close();
        have result == 1 implies region->end <= arena->capacity by {
            intro();
            close();
        }
        close();
        have result == 1 implies 0 <= region->start by {
            intro();
            close();
        }
        close();
        have result == 1 implies region->start < region->end by {
            intro();
            close();
        }
        close();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            have region->start <= k;
            have k < region->end;
            have arena->occupied[k] == 1 by {
                have at(stored, region->start) <= at(stored, k) and at(stored, k) < at(stored, region->end);
                instantiate(forall (j: int32) { at(stored, region->start) <= at(stored, j) and at(stored, j) < at(stored, region->end) implies at(stored, arena->occupied[j]) == at(stored, 1) }, k);
                close();
            }
            close();
        }
        close();
        have forall (k: int32) { result == 1 and 0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have 0 <= k;
            have k < region->start;
            have arena->occupied[k] == old(arena->occupied[k]) by {
                have at(stored, 0) <= at(stored, k) and at(stored, k) < at(stored, region->start);
                instantiate(forall (j: int32) { at(stored, 0) <= at(stored, j) and at(stored, j) < at(stored, region->start) implies at(stored, arena->occupied[j]) == old(arena->occupied[j]) }, k);
                close();
            }
            close();
        }
        close();
        have forall (k: int32) { result == 1 and region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            have region->end <= k;
            have k < arena->capacity;
            have arena->occupied[k] == old(arena->occupied[k]) by {
                have at(stored, region->end) <= at(stored, k) and at(stored, k) < at(stored, arena->capacity);
                instantiate(forall (j: int32) { at(stored, region->end) <= at(stored, j) and at(stored, j) < at(stored, arena->capacity) implies at(stored, arena->occupied[j]) == old(arena->occupied[j]) }, k);
                close();
            }
            close();
        }
        close();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            have region->start <= k;
            have k < region->end;
            have at(stored, region->start) <= at(stored, k) and at(stored, k) < at(stored, region->end);
            instantiate(forall (j: int32) { at(stored, region->start) <= at(stored, j) and at(stored, j) < at(stored, region->end) implies old(arena->occupied[j]) == 0 }, k);
            close();
        }
        close();
        close();
        close();
    }
}

verifying "arena_free.c";

void arena_free(struct region* region) {
    consumes r: arena_region(region);
    consumes st: arena_state(region->arena);
    requires 1 <= st.live;
    requires r.end <= st.capacity;
    produces *region;
    produces after: arena_state(region->arena);

    ensures region->arena == old(region->arena);
    ensures region->start == old(r.start);
    ensures region->end == old(r.end);
    ensures after.live == old(st.live) - 1;
    ensures after.capacity == old(st.capacity);
    ensures region->arena->capacity == old(region->arena->capacity);
    ensures forall (k: int32) {
        region->start <= k and k < region->end implies region->arena->occupied[k] == 0
    };
    ensures forall (k: int32) {
        0 <= k and k < region->start implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
    ensures forall (k: int32) {
        region->end <= k and k < region->arena->capacity implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
} by {
    let { live: n, capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    unfold(arena_cells(region->arena->data, region->arena->occupied, region->arena->capacity));
    have viewable(region->arena->occupied[0..region->arena->capacity]) by {
        close();
    }
    have separate(memory(*region), memory(region->arena->occupied[0..region->arena->capacity])) by {
        close();
    }
    mark unfolded;
    step();
    have separate(statement(0).footprint, memory(region->arena)) by {
        close() using {};
    }
    have region->arena == at(statement(0).entry, region->arena) by {
        preserve(memory(region->arena), statement(0));
    }
    have separate(statement(0).footprint, memory(region->arena->data)) by {
        close() using {};
    }
    have region->arena->data == at(statement(0).entry, region->arena->data) by {
        preserve(memory(region->arena->data), statement(0));
    }
    have separate(statement(0).footprint, memory(region->arena->occupied)) by {
        close() using {};
    }
    have region->arena->occupied == at(statement(0).entry, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(0));
    }
    step();
    have separate(statement(1).footprint, memory(region->arena)) by {
        close() using {};
    }
    have region->arena == at(statement(1).entry, region->arena) by {
        preserve(memory(region->arena), statement(1));
    }
    have separate(statement(1).footprint, memory(region->arena->data)) by {
        close() using {};
    }
    have region->arena->data == at(statement(1).entry, region->arena->data) by {
        preserve(memory(region->arena->data), statement(1));
    }
    have separate(statement(1).footprint, memory(region->arena->occupied)) by {
        close() using {};
    }
    have region->arena->occupied == at(statement(1).entry, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(1));
    }
    step();
    have separate(statement(2).footprint, memory(region->arena)) by {
        close() using {};
    }
    have region->arena == at(statement(2).entry, region->arena) by {
        preserve(memory(region->arena), statement(2));
    }
    have separate(statement(2).footprint, memory(region->arena->data)) by {
        close() using {};
    }
    have region->arena->data == at(statement(2).entry, region->arena->data) by {
        preserve(memory(region->arena->data), statement(2));
    }
    have separate(statement(2).footprint, memory(region->arena->occupied)) by {
        close() using {};
    }
    have region->arena->occupied == at(statement(2).entry, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(2));
    }
    step();
    have separate(statement(3).footprint, memory(region->arena)) by {
        close() using {};
    }
    have region->arena == at(statement(3).entry, region->arena) by {
        preserve(memory(region->arena), statement(3));
    }
    have separate(statement(3).footprint, memory(region->arena->data)) by {
        close() using {};
    }
    have region->arena->data == at(statement(3).entry, region->arena->data) by {
        preserve(memory(region->arena->data), statement(3));
    }
    have separate(statement(3).footprint, memory(region->arena->occupied)) by {
        close() using {};
    }
    have region->arena->occupied == at(statement(3).entry, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(3));
    }
    have arena == region->arena by {
        close();
    }
    have e <= c by {
        close();
    }
    have arena->capacity == c by {
        close();
    }
    have e <= arena->capacity by {
        close();
    }
    have forall (k: int32) { region->start <= k and k < region->start implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have region->start <= k;
        have k < region->start;
        have not k < region->start by {
            close();
        }
        contradiction(k < region->start);
    }
    have viewable(arena->occupied[0..arena->capacity]) by {
        observe(at(unfolded, region->arena->occupied)[0..at(unfolded, region->arena->capacity)]);
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == old(region->arena->occupied[k]) } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        have separate(statement(0).footprint, memory(at(unfolded, region->arena->occupied)[k])) by {
            close() using {};
        }
        have at(statement(0).exit, (let saved: int32* = at(unfolded, region->arena->occupied); saved[k])) == at(statement(0).entry, (let saved: int32* = at(unfolded, region->arena->occupied); saved[k])) by {
            preserve(memory(at(unfolded, region->arena->occupied)[k]), statement(0));
        }
        have separate(statement(1).footprint, memory(at(unfolded, region->arena->occupied)[k])) by {
            close() using {};
        }
        have at(statement(1).exit, (let saved: int32* = at(unfolded, region->arena->occupied); saved[k])) == at(statement(1).entry, (let saved: int32* = at(unfolded, region->arena->occupied); saved[k])) by {
            preserve(memory(at(unfolded, region->arena->occupied)[k]), statement(1));
        }
        have separate(statement(2).footprint, memory(at(unfolded, region->arena->occupied)[k])) by {
            close() using {};
        }
        have at(statement(2).exit, (let saved: int32* = at(unfolded, region->arena->occupied); saved[k])) == at(statement(2).entry, (let saved: int32* = at(unfolded, region->arena->occupied); saved[k])) by {
            preserve(memory(at(unfolded, region->arena->occupied)[k]), statement(2));
        }
        have separate(statement(3).footprint, memory(at(unfolded, region->arena->occupied)[k])) by {
            close() using {};
        }
        have at(statement(3).exit, (let saved: int32* = at(unfolded, region->arena->occupied); saved[k])) == at(statement(3).entry, (let saved: int32* = at(unfolded, region->arena->occupied); saved[k])) by {
            preserve(memory(at(unfolded, region->arena->occupied)[k]), statement(3));
        }
        close();
    }
    let w = fold(arena_clear_window(arena->data, arena->occupied, arena->capacity, region->start, region->end), { next: region->start });
    loop clear_occupied {
        decreases (to_integer(region->end) - to_integer(i));
        owns w: arena_clear_window(arena->data, arena->occupied, arena->capacity, region->start, region->end);
        invariant w.next == i;
        invariant forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) };
        invariant forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) };
        invariant arena->data == at(clear_occupied.entry, arena->data);
        invariant arena->occupied == at(clear_occupied.entry, arena->occupied);
        invariant region->arena == old(region->arena);
        initialize by {
            have w.next == i by {
                close();
            }
            have forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                intro();
                close();
            }
            have forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                intro();
                close();
            }
            have arena->data == at(clear_occupied.entry, arena->data) by {
                close();
            }
            have arena->occupied == at(clear_occupied.entry, arena->occupied) by {
                close();
            }
            have region->arena == old(region->arena) by {
                close();
            }
        }
        maintain by {
            let { next: m } = unfold(w);
            have m == i by {
                close();
            }
            have 0 <= region->start by {
                close();
            }
            have region->start <= m by {
                close();
            }
            have region->start <= i by {
                close();
            }
            have 0 <= i by {
                close() using { at(function.entry, 0) <= at(function.entry, region->start); at(function.entry, region->start) <= at(function.entry, i); };
            }
            have region->end <= arena->capacity by {
                close();
            }
            have i < arena->capacity by {
                apply(integer::int32_less_than_less_equal_transitive(i, region->end, arena->capacity));
            }
            mark opened;
            have contains(memory(*arena), memory(arena->occupied)) by {
                close();
            }
            have separate(memory(arena->occupied), memory(arena->occupied[i])) by {
                apply(selected_array_cell(memory(*arena), memory(arena->occupied), arena->occupied, arena->capacity, i));
            }
            have separate(memory(arena->occupied), memory(at(clear_occupied.entry, arena->occupied)[i])) by {
                rewrite(at(clear_occupied.entry, arena->occupied), arena->occupied);
                close();
            }
            have contains(memory(*arena), memory(arena->data)) by {
                close();
            }
            have separate(memory(arena->data), memory(arena->occupied[i])) by {
                apply(selected_array_cell(memory(*arena), memory(arena->data), arena->occupied, arena->capacity, i));
            }
            have separate(memory(arena->data), memory(at(clear_occupied.entry, arena->occupied)[i])) by {
                rewrite(at(clear_occupied.entry, arena->occupied), arena->occupied);
                close();
            }
            have contains(memory(*region), memory(region->arena)) by {
                close();
            }
            have separate(memory(region->arena), memory(arena->occupied[i])) by {
                apply(selected_array_cell(memory(*region), memory(region->arena), arena->occupied, arena->capacity, i));
            }
            have separate(memory(region->arena), memory(at(clear_occupied.entry, arena->occupied)[i])) by {
                rewrite(at(clear_occupied.entry, arena->occupied), arena->occupied);
                close();
            }
            have contains(memory(*region), memory(region->start)) by { close(); }
            have separate(memory(region->start), memory(arena->occupied[i])) by {
                apply(selected_array_cell(memory(*region), memory(region->start), arena->occupied, arena->capacity, i));
            }
            have contains(memory(*region), memory(region->end)) by { close(); }
            have separate(memory(region->end), memory(arena->occupied[i])) by {
                apply(selected_array_cell(memory(*region), memory(region->end), arena->occupied, arena->capacity, i));
            }
            have contains(memory(*arena), memory(arena->capacity)) by { close(); }
            have separate(memory(arena->capacity), memory(arena->occupied[i])) by {
                apply(selected_array_cell(memory(*arena), memory(arena->capacity), arena->occupied, arena->capacity, i));
            }
            step();
            have at(opened, separate(loop(0).statement(0).footprint, memory(region->start))) by { close(); }
            have region->start == at(opened, region->start) by {
                preserve(at(opened, memory(region->start)), loop(0).statement(0));
            }
            have at(opened, separate(loop(0).statement(0).footprint, memory(region->end))) by { close(); }
            have region->end == at(opened, region->end) by {
                preserve(at(opened, memory(region->end)), loop(0).statement(0));
            }
            have separate(statement(4).statement(0).footprint, memory(arena->occupied)) by {
                close() using {
                    separate(memory(arena->occupied), memory(at(clear_occupied.entry,
                        arena->occupied)[i]));
                };
            }
            have arena->occupied == at(opened, arena->occupied) by {
                preserve(memory(arena->occupied), statement(4).statement(0));
            }
            have separate(statement(4).statement(0).footprint, memory(arena->data)) by {
                close() using {
                    separate(memory(arena->data), memory(at(clear_occupied.entry,
                        arena->occupied)[i]));
                };
            }
            have arena->data == at(opened, arena->data) by {
                preserve(memory(arena->data), statement(4).statement(0));
            }
            have at(opened, separate(loop(0).statement(0).footprint, memory(arena->capacity))) by { close(); }
            have arena->capacity == at(opened, arena->capacity) by {
                preserve(at(opened, memory(arena->capacity)), loop(0).statement(0));
            }
            have separate(statement(4).statement(0).footprint, memory(region->arena)) by {
                close() using {
                    separate(memory(region->arena), memory(at(clear_occupied.entry,
                        arena->occupied)[i]));
                };
            }
            have region->arena == at(opened, region->arena) by {
                preserve(memory(region->arena), statement(4).statement(0));
            }
            mark cleared;
            fold(at(opened, arena_clear_window(arena->data, arena->occupied, arena->capacity, region->start, region->end))[i]);
            step();
            have to_integer(region->start) <= (to_integer(at(opened, i)) + 1) by {
                close() using { to_integer(old(region->start)) <= to_integer(at(opened, i)); to_integer(region->start) == to_integer(old(region->start)); };
            }
            have forall (k: int32) { region->start <= k and to_integer(k) < (to_integer(at(opened, i)) + 1) implies arena->occupied[k] == 0 } by {
                intro();
                intro();
                have region->start <= k;
                have to_integer(k) < (to_integer(at(opened, i)) + 1);
                if k < at(opened, i) {
                    have k < m by {
                        close();
                    }
                    have at(opened, arena->occupied[k]) == 0 by {
                        have at(opened, region->start) <= at(opened, k) and at(opened, k) < at(opened, m);
                        instantiate(forall (j: int32) { at(opened, region->start) <= at(opened, j) and at(opened, j) < at(opened, m) implies at(opened, arena->occupied[j]) == at(opened, 0) }, k);
                        close();
                    }
                    have 0 <= k by {
                        close() using { (at(function.entry, 0) as int32) <= (at(function.entry,
                                region->start) as int32); (region->start as int32) <= (k as int32); (region->start as int32) == (at(opened, region->start) as
                                int32); };
                    }
                    have k < at(opened, arena->capacity) by {
                        close() using { at(region(5).entry, i) < at(region(5).entry, region->end); at(function.entry, region->end) <= at(function.entry,
                                arena->capacity); k < at(region(5).entry, i); };
                    }
                    have at(opened, i) != k by { close() using { k < at(opened, i); }; }
                    have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                        apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k));
                    }
                    have separate(loop(0).statement(0).footprint, memory(at(opened, arena->occupied)[k])) by {
                        close();
                    }
                    have at(loop(0).statement(0).exit, (let saved: int32* = at(opened, arena->occupied); saved[k]))
                        == at(loop(0).statement(0).entry, (let saved: int32* = at(opened, arena->occupied); saved[k])) by {
                        preserve(memory(at(opened, arena->occupied)[k]), loop(0).statement(0));
                    }
                    rewrite(arena->occupied, at(opened, arena->occupied));
                    close();
                } else {
                    have to_integer(k) == to_integer(at(opened, i)) by {
                        close() using { to_integer(k) < (to_integer(at(opened, i)) + 1); not k < at(opened, i); };
                    }
                    rewrite(k, at(opened, i));
                    rewrite(arena->occupied, at(opened, arena->occupied));
                    close();
                }
            }
            have forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                intro();
                have 0 <= k;
                have k < region->start;
                have at(opened, arena->occupied[k]) == at(clear_occupied.entry, arena->occupied[k]) by {
                    have at(opened, 0) <= at(opened, k) and at(opened, k) < at(opened, region->start);
                    instantiate(forall (j: int32) { at(opened, 0) <= at(opened, j) and at(opened, j) < at(opened, region->start) implies at(opened, arena->occupied[j]) == at(clear_occupied.entry, arena->occupied[j]) }, k);
                    close();
                }
                have k < at(opened, i) by {
                    close() using { at(region(3).exit, i) <= at(region(5).entry, i); region->start == at(opened, region->start); k < region->start; };
                }
                have at(opened, i) != k by { close() using { k < at(opened, i); }; }
                have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                    apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k));
                }
                have separate(loop(0).statement(0).footprint, memory(at(opened, arena->occupied)[k])) by {
                    close();
                }
                have at(loop(0).statement(0).exit, (let saved: int32* = at(opened, arena->occupied); saved[k]))
                    == at(loop(0).statement(0).entry, (let saved: int32* = at(opened, arena->occupied); saved[k])) by {
                    preserve(memory(at(opened, arena->occupied)[k]), loop(0).statement(0));
                }
                rewrite(arena->occupied, at(opened, arena->occupied));
                close();
            }
            have forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                intro();
                have region->end <= k;
                have k < arena->capacity;
                have at(opened, arena->occupied[k]) == at(clear_occupied.entry, arena->occupied[k]) by {
                    have at(opened, region->end) <= at(opened, k) and at(opened, k) < at(opened, arena->capacity);
                    instantiate(forall (j: int32) { at(opened, region->end) <= at(opened, j) and at(opened, j) < at(opened, arena->capacity) implies at(opened, arena->occupied[j]) == at(clear_occupied.entry, arena->occupied[j]) }, k);
                    close();
                }
                have at(opened, i) < k by {
                    close() using { region->end <= k; region->end == at(opened, region->end); at(region(5).entry, i) < at(region(5).entry, region->end); };
                }
                have at(opened, i) <= k by {
                    apply(integer::int32_less_than_implies_less_equal(at(opened, i), k));
                }
                have 0 <= k by {
                    close() using { (0 as int32) <= (at(region(5).entry, i) as int32); (at(opened, i) as int32) <= (k as int32); };
                }
                have at(opened, i) != k by { close() using { at(opened, i) < k; }; }
                have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                    apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k));
                }
                have separate(loop(0).statement(0).footprint, memory(at(opened, arena->occupied)[k])) by {
                    close();
                }
                have at(loop(0).statement(0).exit, (let saved: int32* = at(opened, arena->occupied); saved[k]))
                    == at(loop(0).statement(0).entry, (let saved: int32* = at(opened, arena->occupied); saved[k])) by {
                    preserve(memory(at(opened, arena->occupied)[k]), loop(0).statement(0));
                }
                rewrite(arena->occupied, at(opened, arena->occupied));
                close();
            }
            have forall (k: int32) { region->start <= k and k < i implies arena->occupied[k] == 0 } by {
                intro();
                intro();
                have region->start <= k;
                have k < i;
                have to_integer(k) < (to_integer(at(opened, i)) + 1) by {
                    have -2147483648 <= (to_integer(at(opened, i)) + 1) by {
                        close() using { 0 <= to_integer(at(opened, i)); };
                    }
                    have (to_integer(at(opened, i)) + 1) <= 2147483647 by {
                        close() using { to_integer(at(opened, i)) < to_integer(at(region(5).entry,
                                arena->capacity)); to_integer(at(region(5).entry, arena->capacity)) <= 536870911; };
                    }
                    have to_integer((i as int32)) == (to_integer(at(opened, i)) + 1) by {
                        close() using { -2147483648 <= (to_integer(at(opened, i)) + 1); (to_integer(at(opened, i)) + 1) <= 2147483647; };
                    }
                    close() using { to_integer((i as int32)) == (to_integer(at(opened, i)) + 1); to_integer(k) < to_integer((i as int32)); };
                }
                instantiate(forall (j: int32) { region->start <= j and to_integer(j) < (to_integer(at(opened, i)) + 1) implies arena->occupied[j] == 0 }, k);
                close();
            }
            have arena->occupied == old(region->arena->occupied) by {
                close();
            }
            have region->start == old(region->start) by {
                close();
            }
            have forall (k: int32) { old(region->start) <= k and k < i implies (let saved: int32* = old(region->arena->occupied); saved[k]) == 0 } by {
                intro();
                intro();
                have old(region->start) <= k;
                have k < i;
                have region->start <= k and k < i;
                instantiate(forall (j: int32) { region->start <= j and j < i implies arena->occupied[j] == 0 }, k);
                rewrite(old(region->arena->occupied), arena->occupied);
                close();
            }
            let w = fold(arena_clear_window(old(region->arena->data), old(region->arena->occupied), old(region->arena->capacity), old(region->start), old(region->end)), { next: i });
            have region->start <= region->end by {
                close();
            }
            have region->arena == at(opened, region->arena) by {
                have separate(loop(0).statement(1).footprint, memory(region->arena)) by { close(); }
                have region->arena == at(cleared, region->arena) by {
                    preserve(memory(region->arena), loop(0).statement(1));
                }
                close();
            }
            have region->arena == old(region->arena) by {
                close();
            }
            have to_integer(i) == (to_integer(at(opened, i)) + 1) by {
                have -2147483648 <= (to_integer(at(opened, i)) + 1) by {
                    close() using { 0 <= to_integer(at(opened, i)); };
                }
                have (to_integer(at(opened, i)) + 1) <= 2147483647 by {
                    close() using { to_integer(at(opened, i)) < to_integer(at(region(5).entry,
                            arena->capacity)); to_integer(at(region(5).entry, arena->capacity)) <= 536870911; };
                }
                have to_integer(i) == (to_integer(at(opened, i)) + 1) by {
                    close() using { -2147483648 <= (to_integer(at(opened, i)) + 1); (to_integer(at(opened, i)) + 1) <= 2147483647; };
                }
                close();
            }
            have 0 <= (to_integer(region->end) - to_integer(i)) by {
                close() using { to_integer(i) <= to_integer(old(region->end)); to_integer(region->end) == to_integer(old(region->end)); };
            }
            have (to_integer(region->end) - to_integer(i)) < (to_integer(region->end) - to_integer(at(opened, i))) by {
                rewrite(to_integer(i), (to_integer(at(opened, i)) + 1));
                close();
            }
            have w.next == i by {
                close();
            }
            have w.next == i implies forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                close();
            }
            have w.next == i implies forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                intro();
                close();
            }
            have w.next == i implies forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies arena->data == at(clear_occupied.entry, arena->data) by {
                intro();
                intro();
                intro();
                close();
            }
            have w.next == i implies forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies arena->data == at(clear_occupied.entry, arena->data) implies arena->occupied == at(clear_occupied.entry, arena->occupied) by {
                intro();
                intro();
                intro();
                intro();
                close();
            }
            have w.next == i implies forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies arena->data == at(clear_occupied.entry, arena->data) implies arena->occupied == at(clear_occupied.entry, arena->occupied) implies region->arena == old(region->arena) by {
                intro();
                intro();
                intro();
                intro();
                intro();
                close();
            }
        }
    }
    let { next: m } = unfold(w);
    have m <= region->end by {
        close();
    }
    have not i < region->end by {
        close();
    }
    have not m < region->end by {
        close();
    }
    have m == region->end by {
        close() using { at(function.entry, m) <= at(function.entry, region->end); not at(function.entry, m) < at(function.entry, region->end); };
    }
    have region->start <= region->end by {
        close();
    }
    have 0 <= region->end by {
        close() using { at(region(3).exit, i) <= m; at(function.entry, m) <= at(function.entry, region->end); at(function.entry, 0) <= at(function.entry, region->start); };
    }
    have region->end <= arena->capacity by {
        close();
    }
    have forall (k: int32) { region->start <= k and k < region->end implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have region->start <= k;
        have k < region->end;
        have k < m by {
            close();
        }
        instantiate(forall (j: int32) { region->start <= j and j < m implies arena->occupied[j] == 0 }, k);
        close();
    }
    have forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == old(region->arena->occupied[k]) } by {
        intro();
        intro();
        have 0 <= k;
        have k < region->start;
        have arena->occupied[k] == old(region->arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < region->start implies arena->occupied[j] == at(clear_occupied.entry, arena->occupied[j]) }, k);
            close();
        }
        have k < region->end by {
            close() using { at(region(3).exit, i) <= m; at(function.entry, m) <= at(function.entry, region->end); k < at(region(3).exit, i); };
        }
        have k < arena->capacity by {
            apply(integer::int32_less_than_less_equal_transitive(k, region->end, arena->capacity));
        }
        have at(clear_occupied.entry, 0) <= at(clear_occupied.entry, k) and at(clear_occupied.entry, k) < at(clear_occupied.entry, arena->capacity);
        instantiate(forall (j: int32) { at(clear_occupied.entry, 0) <= at(clear_occupied.entry, j) and at(clear_occupied.entry, j) < at(clear_occupied.entry, arena->capacity) implies at(clear_occupied.entry, arena->occupied[j]) == old(region->arena->occupied[j]) }, k);
        close() using {
            arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]);
            at(clear_occupied.entry, arena->occupied[k]) == old(region->arena->occupied[k]);
        };
    }
    have forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == old(region->arena->occupied[k]) } by {
        intro();
        intro();
        have region->end <= k;
        have k < arena->capacity;
        have arena->occupied[k] == old(region->arena->occupied[k]) by {
            instantiate(forall (j: int32) { region->end <= j and j < arena->capacity implies arena->occupied[j] == at(clear_occupied.entry, arena->occupied[j]) }, k);
            close();
        }
        have 0 <= k by {
            close() using { at(function.entry, 0) <= at(function.entry, region->end); at(region(0).entry, region->end) <= k; };
        }
        have at(clear_occupied.entry, 0) <= at(clear_occupied.entry, k) and at(clear_occupied.entry, k) < at(clear_occupied.entry, arena->capacity);
        instantiate(forall (j: int32) { at(clear_occupied.entry, 0) <= at(clear_occupied.entry, j) and at(clear_occupied.entry, j) < at(clear_occupied.entry, arena->capacity) implies at(clear_occupied.entry, arena->occupied[j]) == old(region->arena->occupied[j]) }, k);
        close() using {
            arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]);
            at(clear_occupied.entry, arena->occupied[k]) == old(region->arena->occupied[k]);
        };
    }
    mark cleared;
    have at(cleared, separate(memory(arena->live_regions), memory(region->arena))) by {
        close();
    }
    have at(cleared, separate(memory(arena->live_regions), memory(arena->data))) by {
        close();
    }
    have at(cleared, separate(memory(arena->live_regions), memory(arena->occupied))) by {
        close();
    }
    have 1 <= n by {
        close();
    }
    step();
    have separate(statement(5).footprint, memory(region->arena)) by {
        close() using {
            at(cleared, separate(memory(arena->live_regions), memory(region->arena)));
        };
    }
    have region->arena == at(cleared, region->arena) by {
        preserve(memory(region->arena), statement(5));
    }
    have separate(statement(5).footprint, memory(arena->data)) by {
        close() using {
            at(cleared, separate(memory(arena->live_regions), memory(arena->data)));
        };
    }
    have arena->data == at(cleared, arena->data) by {
        preserve(memory(arena->data), statement(5));
    }
    have separate(statement(5).footprint, memory(arena->occupied)) by {
        close() using {
            at(cleared, separate(memory(arena->live_regions), memory(arena->occupied)));
        };
    }
    have arena->occupied == at(cleared, arena->occupied) by {
        preserve(memory(arena->occupied), statement(5));
    }
    have forall (k: int32) { region->start <= k and k < region->end implies region->arena->occupied[k] == 0 } by {
        intro();
        intro();
        have region->start <= k;
        have k < region->end;
        have 0 <= k by {
            close() using { at(function.entry, 0) <= at(function.entry, region->start); at(region(3).exit, i) <= k; };
        }
        have k < arena->capacity by {
            apply(integer::int32_less_than_less_equal_transitive(k, region->end, arena->capacity));
        }
        have at(cleared, region->start) <= at(cleared, k) and at(cleared, k) < at(cleared, region->end);
        instantiate(forall (j: int32) { at(cleared, region->start) <= at(cleared, j) and at(cleared, j) < at(cleared, region->end) implies at(cleared, arena->occupied[j]) == at(cleared, 0) }, k);
        have contains(memory(*arena), memory(arena->live_regions)) by { close(); }
        have separate(memory(arena->live_regions), memory(arena->occupied[k])) by {
            apply(selected_array_cell(memory(*arena), memory(arena->live_regions), arena->occupied, arena->capacity, k));
        }
        have separate(statement(5).footprint, memory(arena->occupied[k])) by {
            close() using { separate(memory(arena->live_regions), memory(arena->occupied[k])); };
        }
        have arena->occupied[k] == at(cleared, arena->occupied[k]) by {
            preserve(memory(arena->occupied[k]), statement(5));
        }
        rewrite(region->arena, arena);
        close();
    }
    have forall (k: int32) { 0 <= k and k < region->start implies region->arena->occupied[k] == old(region->arena->occupied[k]) } by {
        intro();
        intro();
        have 0 <= k;
        have k < region->start;
        have k < region->end by {
            close() using { at(region(3).exit, i) <= m; at(function.entry, m) <= at(function.entry, region->end); k < at(region(3).exit, i); };
        }
        have k < arena->capacity by {
            apply(integer::int32_less_than_less_equal_transitive(k, region->end, arena->capacity));
        }
        have at(cleared, 0) <= at(cleared, k) and at(cleared, k) < at(cleared, region->start);
        instantiate(forall (j: int32) { at(cleared, 0) <= at(cleared, j) and at(cleared, j) < at(cleared, region->start) implies at(cleared, arena->occupied[j]) == old(region->arena->occupied[j]) }, k);
        have contains(memory(*arena), memory(arena->live_regions)) by { close(); }
        have separate(memory(arena->live_regions), memory(arena->occupied[k])) by {
            apply(selected_array_cell(memory(*arena), memory(arena->live_regions), arena->occupied, arena->capacity, k));
        }
        have separate(statement(5).footprint, memory(arena->occupied[k])) by {
            close() using { separate(memory(arena->live_regions), memory(arena->occupied[k])); };
        }
        have arena->occupied[k] == at(cleared, arena->occupied[k]) by {
            preserve(memory(arena->occupied[k]), statement(5));
        }
        rewrite(region->arena, arena);
        close();
    }
    have forall (k: int32) { region->end <= k and k < arena->capacity implies region->arena->occupied[k] == old(region->arena->occupied[k]) } by {
        intro();
        intro();
        have region->end <= k;
        have k < arena->capacity;
        have 0 <= k by {
            close() using { at(function.entry, 0) <= at(function.entry, region->end); at(region(0).entry, region->end) <= k; };
        }
        have at(cleared, region->end) <= at(cleared, k) and at(cleared, k) < at(cleared, arena->capacity);
        instantiate(forall (j: int32) { at(cleared, region->end) <= at(cleared, j) and at(cleared, j) < at(cleared, arena->capacity) implies at(cleared, arena->occupied[j]) == old(region->arena->occupied[j]) }, k);
        have contains(memory(*arena), memory(arena->live_regions)) by { close(); }
        have separate(memory(arena->live_regions), memory(arena->occupied[k])) by {
            apply(selected_array_cell(memory(*arena), memory(arena->live_regions), arena->occupied, arena->capacity, k));
        }
        have separate(statement(5).footprint, memory(arena->occupied[k])) by {
            close() using { separate(memory(arena->live_regions), memory(arena->occupied[k])); };
        }
        have arena->occupied[k] == at(cleared, arena->occupied[k]) by {
            preserve(memory(arena->occupied[k]), statement(5));
        }
        rewrite(region->arena, arena);
        close();
    }
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    have defined(n - 1) by { close(); }
    let after = fold(arena_state(arena), { live: (n - 1), capacity: c });
    step();
    close();
    have region->start == old(r.start) by {
        close();
    }
    have region->end == old(r.end) by {
        close();
    }
    have to_integer(after.live) == (to_integer(old(st.live)) - 1) by {
        have -2147483648 <= (to_integer(old(st.live)) - 1) by {
            close() using { 0 <= to_integer(old(st.live)); };
        }
        have (to_integer(old(st.live)) - 1) <= 2147483647 by {
            close() using {  };
        }
        have to_integer(after.live) == (to_integer(old(st.live)) - 1) by {
            close() using { -2147483648 <= (to_integer(old(st.live)) - 1); (to_integer(old(st.live)) - 1) <= 2147483647; };
        }
        close();
    }
    have forall (k: int32) { region->start <= k and k < region->end implies region->arena->occupied[k] == 0 } by {
        close();
    }
    have forall (k: int32) { 0 <= k and k < region->start implies region->arena->occupied[k] == old(region->arena->occupied[k]) } by {
        close();
    }
    have forall (k: int32) { region->end <= k and k < region->arena->capacity implies region->arena->occupied[k] == old(region->arena->occupied[k]) } by {
        close();
    }
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
}

verifying "arena_write.c";

void arena_write(struct region* region, int32 index, int32 value) {
    owns r: arena_region(region);
    owns st: arena_state(old(region->arena));
    requires 0 <= index;
    requires defined(r.start + index) and r.start + index < r.end;
    requires r.end <= st.capacity;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures st.capacity == old(st.capacity);
    ensures r.end <= st.capacity;
    ensures st.live == old(st.live);
    ensures region->arena == old(region->arena);
    ensures region->arena->capacity == old(region->arena->capacity);
    ensures region->arena->data == old(region->arena->data);
    ensures region->arena->data[region->start + index] == value;
    ensures region->arena->data[r.start + index] == value;
    ensures forall (k: int32) {
        0 <= k and k < region->arena->capacity implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
} by {
    let { live: n, capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have defined(s + index);
    have s + index < e;
    have s <= s + index;
    have s + index + 1 <= e;
    have region->start == s;
    have region->start + index + 1 <= e;
    have 0 <= region->start + index;
    have region->arena->capacity == c;
    have region->start + index < region->arena->capacity;
    have 0 <= to_integer(region->start + index);
    have to_integer(region->start + index) < to_integer(region->arena->capacity);
    have to_integer(s) <= to_integer(s + index);
    have to_integer(s + index) < to_integer(e);
    have separate(
        memory(*region),
        memory(*(region->arena->data + (region->start + index)))
    );
    have separate(memory(*region->arena), memory(region->arena->data[0..region->arena->capacity])) by close();
    have separate(memory(*region->arena), memory(region->arena->occupied[0..region->arena->capacity])) by close();
    mark w;
    step();
    have separate(statement(0).footprint, memory(region->arena)) by { close(); }
    have region->arena == at(statement(0).entry, region->arena) by {
        preserve(memory(region->arena), statement(0));
    }
    have separate(statement(0).footprint, memory(region->arena->data)) by { close(); }
    have region->arena->data == at(statement(0).entry, region->arena->data) by {
        preserve(memory(region->arena->data), statement(0));
    }
    have separate(statement(0).footprint, memory(region->arena->occupied)) by { close(); }
    have region->arena->occupied == at(statement(0).entry, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(0));
    }
    step();
    have separate(statement(1).footprint, memory(region->arena)) by { close(); }
    have region->arena == at(statement(1).entry, region->arena) by {
        preserve(memory(region->arena), statement(1));
    }
    have separate(statement(1).footprint, memory(region->arena->data)) by { close(); }
    have region->arena->data == at(statement(1).entry, region->arena->data) by {
        preserve(memory(region->arena->data), statement(1));
    }
    have separate(statement(1).footprint, memory(region->arena->occupied)) by { close(); }
    have region->arena->occupied == at(statement(1).entry, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(1));
    }
    mark before_access;
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena)));
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->data)));
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->occupied)));
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->capacity)));
    step();
    have separate(statement(2).footprint, memory(region->arena->capacity)) by {
        close();
    }
    have region->arena->capacity == at(before_access, region->arena->capacity) by {
        preserve(memory(region->arena->capacity), statement(2));
    }
    have separate(statement(2).footprint, memory(region->arena)) by { close(); }
    have region->arena == at(before_access, region->arena) by {
        preserve(memory(region->arena), statement(2));
    }
    have separate(statement(2).footprint, memory(region->arena->data)) by { close(); }
    have region->arena->data == at(before_access, region->arena->data) by {
        preserve(memory(region->arena->data), statement(2));
    }
    have separate(statement(2).footprint, memory(region->arena->occupied)) by { close(); }
    have region->arena->occupied == at(before_access, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(2));
    }

    have region->arena == old(region->arena);
    have region->arena->data == old(region->arena->data);

    have forall (k: int32) {
        0 <= k and k < at(w, region->arena->capacity) implies
            at(w, region->arena->occupied[k]) == region->arena->occupied[k]
    } by {
        intro();
        intro();
        have 0 <= k;
        have k < at(w, region->arena->capacity);
        have k < region->arena->capacity by { close(); }
        have contains(memory(region->arena->occupied[0..region->arena->capacity]), memory(region->arena->occupied[k])) by {
            apply(separation::contains_element(region->arena->occupied, 0, region->arena->capacity, k));
        }
        have 0 <= at(before_access, region->start + index) by { close(); }
        have at(before_access, region->start + index) < region->arena->capacity by { close(); }
        have 0 <= to_integer(at(before_access, region->start + index)) by { close(); }
        have to_integer(at(before_access, region->start + index)) < to_integer(region->arena->capacity) by { close(); }
        have at(before_access, region->arena->data) == region->arena->data by { close(); }
        have contains(memory(at(before_access, region->arena->data)[0..region->arena->capacity]), memory(at(before_access, region->arena->data)[at(before_access, region->start + index)])) by {
            apply(separation::contains_element(at(before_access, region->arena->data), 0, region->arena->capacity, at(before_access, region->start + index)));
        }
        have contains(memory(region->arena->data[0..region->arena->capacity]), memory(at(before_access, region->arena->data)[at(before_access, region->start + index)])) by { rewrite(region->arena->data, at(before_access, region->arena->data)); close(); }
        have separate(memory(at(before_access, region->arena->data)[at(before_access, region->start + index)]), memory(region->arena->occupied[k])) by {
            apply(separation::separate_symm(memory(region->arena->occupied[0..region->arena->capacity]), memory(region->arena->data[0..region->arena->capacity])));
            apply(separation::separate_restrict(memory(region->arena->data[0..region->arena->capacity]), memory(region->arena->occupied[0..region->arena->capacity]), memory(at(before_access, region->arena->data)[at(before_access, region->start + index)]), memory(region->arena->occupied[k])));
        }
        have separate(statement(0).footprint, memory(region->arena->occupied[k])) by { close(); }
        have at(statement(0).exit, region->arena->occupied[k]) == at(statement(0).entry, region->arena->occupied[k]) by {
            preserve(memory(region->arena->occupied[k]), statement(0));
        }
        have separate(statement(1).footprint, memory(region->arena->occupied[k])) by { close(); }
        have at(statement(1).exit, region->arena->occupied[k]) == at(statement(1).entry, region->arena->occupied[k]) by {
            preserve(memory(region->arena->occupied[k]), statement(1));
        }
        have separate(statement(2).footprint, memory(region->arena->occupied[k])) by { close(); }
        have at(statement(2).exit, region->arena->occupied[k]) == at(statement(2).entry, region->arena->occupied[k]) by {
            preserve(memory(region->arena->occupied[k]), statement(2));
        }
        close();
    }
    have region->arena->capacity == old(region->arena->capacity) by close();
    have separate(memory(*region->arena), memory(region->arena->data[0..region->arena->capacity])) by {
        rewrite(region->arena->capacity, old(region->arena->capacity));
        rewrite(region->arena->data, old(region->arena->data));
        rewrite(region->arena, old(region->arena));
        close();
    }
    have region->arena->occupied == old(region->arena->occupied) by close();
    have separate(memory(*region->arena), memory(region->arena->occupied[0..region->arena->capacity])) by {
        rewrite(region->arena->capacity, old(region->arena->capacity));
        rewrite(region->arena->occupied, old(region->arena->occupied));
        rewrite(region->arena, old(region->arena));
        close();
    }
    have separate(memory(region->arena->occupied[0..region->arena->capacity]), memory(region->arena->data[0..region->arena->capacity])) by {
        rewrite(region->arena->capacity, old(region->arena->capacity));
        rewrite(region->arena->occupied, old(region->arena->occupied));
        rewrite(region->arena->data, old(region->arena->data));
        close();
    }
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
    step_until(function.exit);
    close();
}

verifying "arena_read.c";

int32 arena_read(struct region* region, int32 index) {
    owns r: arena_region(region);
    owns st: arena_state(old(region->arena));
    requires 0 <= index;
    requires defined(r.start + index) and r.start + index < r.end;
    requires r.end <= st.capacity;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures st.capacity == old(st.capacity);
    ensures r.end <= st.capacity;
    ensures st.live == old(st.live);
    ensures region->arena == old(region->arena);
    ensures region->arena->capacity == old(region->arena->capacity);
    ensures region->arena->data == old(region->arena->data);
    ensures result == region->arena->data[region->start + index];
    ensures result == old(region->arena->data[region->start + index]);
    ensures result == old(region->arena->data[r.start + index]);
    ensures forall (k: int32) {
        0 <= k and k < region->arena->capacity implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
} by {
    let { live: n, capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have defined(s + index);
    have s + index < e;
    have s <= s + index;
    have s + index + 1 <= e;
    have region->start + index + 1 <= e;
    have s + index < c;
    have region->start + index < region->arena->capacity;
    have 0 <= to_integer(s) + to_integer(index) by {
        close() using { 0 <= s; 0 <= index; };
    }
    have to_integer(region->start + index) == to_integer(s) + to_integer(index) by {
        rewrite(region->start, s);
        apply(click::integer::int32_add_to_integer(s, index));
    }
    have 0 <= to_integer(region->start + index) by {
        rewrite(to_integer(region->start + index), to_integer(s) + to_integer(index));
        close();
    }
    have to_integer(region->start + index) < to_integer(region->arena->capacity);
    have to_integer(s) <= to_integer(s + index);
    have to_integer(s + index) < to_integer(e);
    mark w;
    step();
    have separate(statement(0).footprint, memory(region->arena)) by { close(); }
    have region->arena == at(statement(0).entry, region->arena) by {
        preserve(memory(region->arena), statement(0));
    }
    have separate(statement(0).footprint, memory(region->arena->data)) by { close(); }
    have region->arena->data == at(statement(0).entry, region->arena->data) by {
        preserve(memory(region->arena->data), statement(0));
    }
    have separate(statement(0).footprint, memory(region->arena->occupied)) by { close(); }
    have region->arena->occupied == at(statement(0).entry, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(0));
    }
    step();
    have separate(statement(1).footprint, memory(region->arena)) by { close(); }
    have region->arena == at(statement(1).entry, region->arena) by {
        preserve(memory(region->arena), statement(1));
    }
    have separate(statement(1).footprint, memory(region->arena->data)) by { close(); }
    have region->arena->data == at(statement(1).entry, region->arena->data) by {
        preserve(memory(region->arena->data), statement(1));
    }
    have separate(statement(1).footprint, memory(region->arena->occupied)) by { close(); }
    have region->arena->occupied == at(statement(1).entry, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(1));
    }
    mark before_access;
    step();
    have region->arena == at(before_access, region->arena) by { close(); }
    have region->arena->data == at(before_access, region->arena->data) by { close(); }
    have region->arena->occupied == at(before_access, region->arena->occupied) by { close(); }
    have forall (k: int32) {
        0 <= k and k < at(w, region->arena->capacity) implies
            at(w, region->arena->occupied[k]) == region->arena->occupied[k]
    } by {
        intro();
        intro();
        have 0 <= k;
        have k < at(w, region->arena->capacity);
        close();
    }
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
    close();
}

verifying "arena_destroy.c";

void arena_destroy(struct arena* arena) {
    consumes st: arena_state(arena);
    requires forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    };
    produces *arena;

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
    unfold(arena_cells(arena->data, arena->occupied, arena->capacity)[..]);
    step_until(function.exit);
    close();
}

verifying "arena_region_length.c";

int32 arena_region_length(struct region* region) {
    owns r: arena_region(region);
    owns st: arena_state(old(region->arena));
    ensures result == r.end - r.start;
    ensures st.live == old(st.live);
    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
} by {
    let { live: n } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have region->start == s by close();
    step_until(function.exit);
    have result == e - s;
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: region->arena->capacity });
    close();
}

verifying "arena_pipeline.c";

int32 arena_pipeline(
    struct arena* arena,
    struct region* first,
    struct region* second,
    struct region* combined
) {
    owns *arena;
    owns *first;
    owns *second;
    owns *combined;

    ensures result == 0 or result == 33;
} by {
    step();
    step();
    step();
    step();
    step();
    let { outcome: o0 } = step(arena_init);
    step();
    if at(region(7).entry, initialized) == at(region(7).entry, 0) {
        step();
        have o0.model == ArenaInitOutcome::Failure() by close();
        unfold(o0);
        step();
        close();
        have result == 0 or result == 33 by {
            close();
        }
        close();
        close();
        close();
        close();
    } else {
        step();
        step();
    }
    have initialized == 1 by {
        cases {
            initialized == 0 => {
                contradiction(initialized == 0);
            }
            initialized == 1 => {
                close();
            }
        }
    }
    have o0.model == ArenaInitOutcome::Success(0, 8) by close();
    let { state: s0 } = unfold(o0);
    have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        instantiate(forall (j: int32) { initialized == 1 and 0 <= j and j < arena->capacity implies arena->occupied[j] == 0 }, k);
        close();
    }
    mark a1;
    let { outcome: o1 } = step(arena_alloc, { st: s0 });
    mark after_first_alloc;
    step();
    have separate(memory(allocated), memory(first->arena)) by { close(); }
    have separate(statement(7).assignment(allocated, 0).footprint, memory(first->arena)) by {
        close() using { separate(memory(allocated), memory(first->arena)); };
    }
    have first->arena == at(after_first_alloc, first->arena) by {
        preserve(memory(first->arena), statement(7).assignment(allocated, 0));
    }
    have allocated == 1 implies first->arena == arena by {
        intro();
        have at(after_first_alloc, first->arena) == arena;
        close();
    }
    have arena->capacity == at(a1, arena->capacity) by {
        close();
    }
    if at(region(12).entry, allocated) == at(region(12).entry, 0) {
        step();
        have o1.model == ArenaAllocOutcome::Failure() by close();
        have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            have arena->occupied[k] == at(a1, arena->occupied[k]) by {
                instantiate(forall (j: int32) { allocated == 0 and 0 <= j and j < arena->capacity implies arena->occupied[j] == at(a1, arena->occupied[j]) }, k);
                close();
            }
            have k < at(a1, arena->capacity) by {
                close();
            }
            have at(a1, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(a1, arena->capacity) implies at(a1, arena->occupied[j]) == 0 }, k);
                close();
            }
            close();
        }
        step(arena_destroy, { st: s0 });
        unfold(o1);
        step();
        close();
        have result == 0 or result == 33 by {
            close();
        }
        close();
        close();
        close();
        close();
    } else {
        step();
        step();
    }
    have allocated == 1 by {
        cases {
            allocated == 0 => {
                contradiction(allocated == 0);
            }
            allocated == 1 => {
                close();
            }
        }
    }
    have o1.model == ArenaAllocOutcome::Success(first->start, first->end) by close();
    have first->end <= arena->capacity by close();
    let { allocated: r1 } = unfold(o1);
    have first->arena == arena by close();
    mark z1;
    have r1.start == at(z1, first->start) by {
        close();
    }
    have r1.end == at(z1, first->end) by {
        close();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        have k < at(z1, first->start) or at(z1, first->end) <= k;
        have k < at(a1, arena->capacity) by {
            close();
        }
        have at(a1, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(a1, arena->capacity) implies at(a1, arena->occupied[j]) == 0 }, k);
            close();
        }
        cases {
            k < at(z1, first->start) => {
                have k < first->start by {
                    close();
                }
                have arena->occupied[k] == at(a1, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { allocated == 1 and 0 <= j and j < first->start implies arena->occupied[j] == at(a1, arena->occupied[j]) }, k);
                    close();
                }
                close();
            }
            at(z1, first->end) <= k => {
                have first->end <= k by {
                    close();
                }
                have arena->occupied[k] == at(a1, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { allocated == 1 and first->end <= j and j < arena->capacity implies arena->occupied[j] == at(a1, arena->occupied[j]) }, k);
                    close();
                }
                close();
            }
        }
    }
    have at(a1, s0.live) == 0 by {
        close();
    }
    have s0.live == 1 by {
        close();
    }
    // Expose only the selected region to record its descriptor separation.
    // Keep the region folded across the call; preserve the selected read explicitly.
    let { live: retained_live, capacity: retained_capacity } = unfold(s0);
    let { start: retained_first_start, end: retained_first_end } = unfold(r1);
    let s0 = fold(arena_state(arena), { live: retained_live, capacity: retained_capacity }) {
        requires arena->capacity <= 536870911 by close();
        requires arena->capacity == (retained_capacity as int32) by close();
        requires arena->live_regions == (retained_live as int32) by close();
        requires 0 <= (retained_live as int32) by close();
        requires separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity])) by close();
        requires separate(memory(*arena), memory(arena->data[0..arena->capacity])) by close();
        requires separate(memory(*arena), memory(arena->occupied[0..arena->capacity])) by close();
    };
    have separate(s0, memory(*first)) by { close(); }
    have separate(memory(*second), memory(*first)) by { close(); }
    have separate(s0 * memory(*second), memory(*first)) by {
        apply(separation::separate_star(s0, memory(*second), memory(*first)));
    }
    let r1 = fold(arena_region(first), { start: retained_first_start, end: retained_first_end }) {
        requires first->start == (retained_first_start as int32) by close();
        requires first->end == (retained_first_end as int32) by close();
        requires 0 <= (retained_first_start as int32) by close();
        requires (retained_first_start as int32) < (retained_first_end as int32) by close();
    };
    mark a2;
    let { outcome: o2 } = step(arena_alloc, { st: s0 });
    have contains(at(a2, s0) * memory(*second), statement(9).call(0).footprint) by { close(); }
    have contains(memory(*first), memory(first->arena)) by { normalize(); }
    have separate(statement(9).call(0).footprint, memory(first->arena)) by {
        apply(separation::separate_restrict(at(a2, s0) * memory(*second), memory(*first), statement(9).call(0).footprint, memory(first->arena)));
    }
    have first->arena == at(a2, first->arena) by {
        preserve(memory(first->arena), statement(9).call(0));
    }
    mark after_second_alloc;
    step();
    have separate(memory(allocated), memory(second->arena)) by { close(); }
    have separate(statement(9).assignment(allocated, 0).footprint, memory(second->arena)) by {
        close() using { separate(memory(allocated), memory(second->arena)); };
    }
    have second->arena == at(after_second_alloc, second->arena) by {
        preserve(memory(second->arena), statement(9).assignment(allocated, 0));
    }
    have allocated == 1 implies second->arena == arena by {
        intro();
        have at(after_second_alloc, second->arena) == arena;
        close();
    }
    have arena->capacity == at(a2, arena->capacity) by {
        close();
    }
    if at(region(18).entry, allocated) == at(region(18).entry, 0) {
        step();
        have o2.model == ArenaAllocOutcome::Failure() by close();
        have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            have k < at(z1, first->start) or at(z1, first->end) <= k;
            have arena->occupied[k] == at(a2, arena->occupied[k]) by {
                instantiate(forall (j: int32) { allocated == 0 and 0 <= j and j < arena->capacity implies arena->occupied[j] == at(a2, arena->occupied[j]) }, k);
                close();
            }
            have k < at(a2, arena->capacity) by {
                close();
            }
            have at(a2, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(a2, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(a2, arena->occupied[j]) == 0 }, k);
                close();
            }
            close();
        }
        have at(a2, s0.live) == 1 by {
            close();
        }
        have s0.live == 1 by {
            close();
        }
        have r1.end <= at(z1, arena->capacity) by {
            close();
        }
        have s0.capacity == arena->capacity by {
            close();
        }
        have r1.end <= s0.capacity by {
            close();
        }
        have 1 <= s0.live by {
            close() using { (at(region(19).entry, s0.live) as int32) == (at(region(19).entry, 1) as
                    int32); };
        }
        have first->arena == arena by {
            close();
        }
        mark f1;
        let { after: g1 } = step(arena_free, { r: r1, st: s0 });
        have first->arena == arena by {
            close();
        }
        have first->arena->capacity == at(f1, first->arena->capacity) by {
            close();
        }
        have arena->capacity == first->arena->capacity by {
            close();
        }
        have at(f1, first->arena->capacity) == at(f1, arena->capacity) by {
            close();
        }
        have arena->capacity == at(f1, arena->capacity) by {
            close();
        }
        have first->start == at(z1, first->start) by {
            close();
        }
        have first->end == at(z1, first->end) by {
            close();
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            have k < first->start implies arena->occupied[k] == 0 by {
                intro();
                have first->arena->occupied[k] == at(f1, first->arena->occupied[k]) by {
                    instantiate(forall (j: int32) { 0 <= j and j < first->start implies first->arena->occupied[j] == at(f1, first->arena->occupied[j]) }, k);
                    close();
                }
                have at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]) by {
                    close();
                }
                have k < at(f1, arena->capacity) by {
                    close();
                }
                have k < at(z1, first->start) by {
                    close();
                }
                have k < at(z1, first->start) or at(z1, first->end) <= k by {
                    close();
                }
                have at(f1, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) { 0 <= j and j < at(f1, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(f1, arena->occupied[j]) == 0 }, k);
                    close();
                }
                normalize() using {
                    first->arena == arena;
                    first->arena->occupied[k] == at(f1, first->arena->occupied[k]);
                    at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]);
                    at(f1, arena->occupied[k]) == 0;
                };
            }
            have first->start <= k and k < first->end implies arena->occupied[k] == 0 by {
                intro();
                have first->start <= k;
                have k < first->end;
                have arena->occupied[k] == 0 by {
                    instantiate(forall (j: int32) { first->start <= j and j < first->end implies first->arena->occupied[j] == 0 }, k);
                    normalize() using {
                        first->arena == arena;
                        first->arena->occupied[k] == 0;
                    };
                }
                close();
            }
            have first->end <= k implies arena->occupied[k] == 0 by {
                intro();
                have k < first->arena->capacity by {
                    close();
                }
                have first->arena->occupied[k] == at(f1, first->arena->occupied[k]) by {
                    instantiate(forall (j: int32) { first->end <= j and j < first->arena->capacity implies first->arena->occupied[j] == at(f1, first->arena->occupied[j]) }, k);
                    close();
                }
                have at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]) by {
                    close();
                }
                have k < at(f1, arena->capacity) by {
                    close();
                }
                have at(z1, first->end) <= k by {
                    close();
                }
                have k < at(z1, first->start) or at(z1, first->end) <= k by {
                    close();
                }
                have at(f1, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) { 0 <= j and j < at(f1, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(f1, arena->occupied[j]) == 0 }, k);
                    close();
                }
                normalize() using {
                    first->arena == arena;
                    first->arena->occupied[k] == at(f1, first->arena->occupied[k]);
                    at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]);
                    at(f1, arena->occupied[k]) == 0;
                };
            }
            if k < first->start {
                have k < first->start by {
                    close();
                }
                have arena->occupied[k] == 0; close();
            } else {
                have first->start <= k by {
                    close();
                }
                if k < first->end {
                    have first->start <= k and k < first->end by {
                        close();
                    }
                    have arena->occupied[k] == 0; close();
                } else {
                    have first->end <= k by {
                        close();
                    }
                    have arena->occupied[k] == 0; close();
                }
            }
        }
        step(arena_destroy, { st: g1 });
        unfold(o2);
        step();
        close();
        have result == 0 or result == 33 by {
            close();
        }
        close();
        close();
        close();
        close();
    } else {
        step();
        step();
    }
    have allocated == 1 by {
        cases {
            allocated == 0 => {
                contradiction(allocated == 0);
            }
            allocated == 1 => {
                close();
            }
        }
    }
    have o2.model == ArenaAllocOutcome::Success(second->start, second->end) by close();
    have second->end <= arena->capacity by close();
    let { allocated: r2 } = unfold(o2);
    have second->arena == arena by close();
    have at(a2, s0.live) == 1 by {
        close();
    }
    have s0.live == 2 by {
        close();
    }
    mark z2;
    have r2.start == at(z2, second->start) by {
        close();
    }
    have r2.end == at(z2, second->end) by {
        close();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) and (k < at(z2, second->start) or at(z2, second->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        have k < at(z1, first->start) or at(z1, first->end) <= k;
        have k < at(z2, second->start) or at(z2, second->end) <= k;
        have k < at(a2, arena->capacity) by {
            close();
        }
        have at(a2, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(a2, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(a2, arena->occupied[j]) == 0 }, k);
            close();
        }
        cases {
            k < at(z2, second->start) => {
                have k < second->start by {
                    close();
                }
                have arena->occupied[k] == at(a2, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { allocated == 1 and 0 <= j and j < second->start implies arena->occupied[j] == at(a2, arena->occupied[j]) }, k);
                    close();
                }
                close();
            }
            at(z2, second->end) <= k => {
                have second->end <= k by {
                    close();
                }
                have arena->occupied[k] == at(a2, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { allocated == 1 and second->end <= j and j < arena->capacity implies arena->occupied[j] == at(a2, arena->occupied[j]) }, k);
                    close();
                }
                close();
            }
        }
    }
    have first->arena == arena by {
        close();
    }
    have r1.start < r1.end by close();
    have r1.end <= at(z1, arena->capacity) by {
        close();
    }
    have s0.capacity == arena->capacity by {
        close();
    }
    have arena->capacity == at(z1, arena->capacity) by {
        close();
    }
    have r1.end <= s0.capacity by {
        close();
    }
    have first->arena == arena by {
        close();
    }
    let { live: w1_live, capacity: w1_capacity } = unfold(s0);
    let { start: w1_start, end: w1_end } = unfold(r2);
    let s0 = fold(arena_state(arena), { live: w1_live, capacity: w1_capacity });
    have separate(r1, memory(*second)) by { close(); }
    have separate(s0, memory(*second)) by { close(); }
    have separate(r1 * s0, memory(*second)) by {
        apply(separation::separate_star(r1, s0, memory(*second)));
    }
    let r2 = fold(arena_region(second), { start: w1_start, end: w1_end });
    mark w1;
    step(arena_write, { r: r1, st: s0 }) {
        requires 0 <= 0 by normalize();
        requires r1.end <= s0.capacity by close();
        requires defined(r1.start + 0) and (to_integer(r1.start) + to_integer(0)) < to_integer(r1.end) by {
            all {
                defined(r1.start + 0) => {
                    normalize();
                }
                (to_integer(r1.start) + to_integer(0)) < to_integer(r1.end) => {
                    close() using { to_integer(r1.start) < to_integer(r1.end); };
                }
            }
        }
    }
    have contains(at(w1, r1) * at(w1, s0), statement(11).footprint) by { close(); }
    have contains(memory(*second), memory(second->arena)) by { normalize(); }
    have separate(statement(11).footprint, memory(second->arena)) by {
        apply(separation::separate_restrict(at(w1, r1) * at(w1, s0), memory(*second), statement(11).footprint, memory(second->arena)));
    }
    have second->arena == at(w1, second->arena) by {
        preserve(memory(second->arena), statement(11));
    }
    have r1.start == at(w1, r1.start) by {
        close();
    }
    have at(w1, r1.start) == at(z1, first->start) by {
        close();
    }
    have r1.start == at(z1, first->start) by {
        close() using {
            r1.start == at(w1, r1.start);
            at(w1, r1.start) == at(z1, first->start);
        };
    }
    have r1.end == at(w1, r1.end) by {
        close();
    }
    have at(w1, r1.end) == at(z1, first->end) by {
        close();
    }
    have r1.end == at(z1, first->end) by {
        close() using {
            r1.end == at(w1, r1.end);
            at(w1, r1.end) == at(z1, first->end);
        };
    }
    have s0.live == at(w1, s0.live) by {
        close();
    }
    have at(w1, s0.live) == 2 by {
        close();
    }
    have s0.live == 2 by {
        close() using {
            s0.live == at(w1, s0.live);
            at(w1, s0.live) == 2;
        };
    }
    have r2.start == at(w1, r2.start) by {
        close();
    }
    have at(w1, r2.start) == at(z2, second->start) by {
        close();
    }
    have r2.start == at(z2, second->start) by {
        close() using {
            r2.start == at(w1, r2.start);
            at(w1, r2.start) == at(z2, second->start);
        };
    }
    have r2.end == at(w1, r2.end) by {
        close();
    }
    have at(w1, r2.end) == at(z2, second->end) by {
        close();
    }
    have r2.end == at(z2, second->end) by {
        close() using {
            r2.end == at(w1, r2.end);
            at(w1, r2.end) == at(z2, second->end);
        };
    }
    have first->arena == arena by {
        close();
    }
    have first->arena->capacity == at(w1, first->arena->capacity) by {
        close();
    }
    have arena->capacity == first->arena->capacity by {
        close();
    }
    have at(w1, first->arena->capacity) == at(w1, arena->capacity) by {
        close();
    }
    have arena->capacity == at(w1, arena->capacity) by {
        close();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) and (k < at(z2, second->start) or at(z2, second->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        have k < at(z1, first->start) or at(z1, first->end) <= k;
        have k < at(z2, second->start) or at(z2, second->end) <= k;
        have k < first->arena->capacity by {
            close();
        }
        have first->arena->occupied[k] == at(w1, first->arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < first->arena->capacity implies first->arena->occupied[j] == at(w1, first->arena->occupied[j]) }, k);
            close();
        }
        have at(w1, first->arena->occupied[k]) == at(w1, arena->occupied[k]) by {
            close();
        }
        have k < at(w1, arena->capacity) by {
            close();
        }
        have at(w1, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(w1, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(w1, arena->occupied[j]) == 0 }, k);
            close();
        }
        normalize() using {
            first->arena->occupied[k] == at(w1, first->arena->occupied[k]);
            at(w1, first->arena->occupied[k]) == at(w1, arena->occupied[k]);
            at(w1, arena->occupied[k]) == 0;
            first->arena == arena;
        };
    }
    have second->arena == arena by {
        close();
    }
    have r2.start < r2.end by close();
    have r2.end <= at(z2, arena->capacity) by {
        close();
    }
    have s0.capacity == at(w1, s0.capacity) by {
        close();
    }
    have at(w1, s0.capacity) == at(w1, arena->capacity) by {
        close();
    }
    have s0.capacity == arena->capacity by {
        close();
    }
    have arena->capacity == at(z2, arena->capacity) by {
        close();
    }
    have r2.end <= s0.capacity by {
        close();
    }
    have first->arena->data == second->arena->data by {
        close();
    }
    let { live: w2_live, capacity: w2_capacity } = unfold(s0);
    let { start: w2_start, end: w2_end } = unfold(r1);
    mark w2_open;
    let s0 = fold(arena_state(arena), { live: w2_live, capacity: w2_capacity });
    have separate(r2, memory(*first)) by { close(); }
    have separate(s0, memory(*first)) by { close(); }
    have separate(r2 * s0, memory(*first)) by {
        apply(separation::separate_star(r2, s0, memory(*first)));
    }
    have separate(r2, memory(at(w2_open, arena->data)[(w2_start as int32)..(w2_end as int32)])) by { close(); }
    have separate(s0, memory(at(w2_open, arena->data)[(w2_start as int32)..(w2_end as int32)])) by { close(); }
    have separate(r2 * s0, memory(at(w2_open, arena->data)[(w2_start as int32)..(w2_end as int32)])) by {
        apply(separation::separate_star(r2, s0, memory(at(w2_open, arena->data)[(w2_start as int32)..(w2_end as int32)])));
    }
    have (w2_start as int32) <= ((first->start + 0) as int32) by { close(); }
    have ((first->start + 0) as int32) < (w2_end as int32) by { close(); }
    have defined(first->start + 0) by { close(); }
    have contains(memory(at(w2_open, arena->data)[(w2_start as int32)..(w2_end as int32)]), memory(at(w2_open, arena->data)[first->start + 0])) by {
        apply(separation::contains_element(at(w2_open, arena->data), (w2_start as int32), (w2_end as int32), first->start + 0));
    }
    have contains(r2 * s0, r2 * s0) by { apply(separation::contains_refl(r2 * s0)); }
    have separate(r2 * s0, memory(at(w2_open, arena->data)[first->start + 0])) by {
        apply(separation::separate_restrict(r2 * s0, memory(at(w2_open, arena->data)[(w2_start as int32)..(w2_end as int32)]), r2 * s0, memory(at(w2_open, arena->data)[first->start + 0])));
    }
    let r1 = fold(arena_region(first), { start: w2_start, end: w2_end });
    have first->arena->data == at(w2_open, arena->data) by {
        rewrite(first->arena, arena);
        close();
    }
    mark w2;
    step(arena_write, { r: r2, st: s0 }) {
        requires 0 <= 0 by normalize();
        requires r2.end <= s0.capacity by close();
        requires defined(r2.start + 0) and (to_integer(r2.start) + to_integer(0)) < to_integer(r2.end) by {
            all {
                defined(r2.start + 0) => {
                    normalize();
                }
                (to_integer(r2.start) + to_integer(0)) < to_integer(r2.end) => {
                    close() using { to_integer(r2.start) < to_integer(r2.end); };
                }
            }
        }
    }
    have contains(at(w2, r2) * at(w2, s0), statement(12).footprint) by { close(); }
    have contains(memory(*first), memory(first->arena)) by { close(); }
    have separate(statement(12).footprint, memory(first->arena)) by {
        apply(separation::separate_restrict(at(w2, r2) * at(w2, s0), memory(*first), statement(12).footprint, memory(first->arena)));
    }
    have first->arena == at(w2, first->arena) by {
        preserve(memory(first->arena), statement(12));
    }
    have r1.start == at(w2, r1.start) by {
        close();
    }
    have at(w2, r1.start) == at(z1, first->start) by {
        close();
    }
    have r1.start == at(z1, first->start) by {
        close() using {
            r1.start == at(w2, r1.start);
            at(w2, r1.start) == at(z1, first->start);
        };
    }
    have r1.end == at(w2, r1.end) by {
        close();
    }
    have at(w2, r1.end) == at(z1, first->end) by {
        close();
    }
    have r1.end == at(z1, first->end) by {
        close() using {
            r1.end == at(w2, r1.end);
            at(w2, r1.end) == at(z1, first->end);
        };
    }
    have s0.live == at(w2, s0.live) by {
        close();
    }
    have at(w2, s0.live) == 2 by {
        close();
    }
    have s0.live == 2 by {
        close();
    }
    have r2.start == at(w2, r2.start) by {
        close();
    }
    have at(w2, r2.start) == at(z2, second->start) by {
        close();
    }
    have r2.start == at(z2, second->start) by {
        close() using {
            r2.start == at(w2, r2.start);
            at(w2, r2.start) == at(z2, second->start);
        };
    }
    have r2.end == at(w2, r2.end) by {
        close();
    }
    have at(w2, r2.end) == at(z2, second->end) by {
        close();
    }
    have r2.end == at(z2, second->end) by {
        close() using {
            r2.end == at(w2, r2.end);
            at(w2, r2.end) == at(z2, second->end);
        };
    }
    have second->arena == arena by {
        close();
    }
    have second->arena->capacity == at(w2, second->arena->capacity) by {
        close();
    }
    have arena->capacity == second->arena->capacity by {
        close();
    }
    have at(w2, second->arena->capacity) == at(w2, arena->capacity) by {
        close();
    }
    have arena->capacity == at(w2, arena->capacity) by {
        close();
    }
    have s0.capacity == at(w2, s0.capacity) by {
        close();
    }
    have s0.capacity == arena->capacity by {
        normalize() using {
            s0.capacity == at(w2, s0.capacity);
            at(w2, s0.capacity) == at(w2, arena->capacity);
            arena->capacity == at(w2, arena->capacity);
        };
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) and (k < at(z2, second->start) or at(z2, second->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        have k < at(z1, first->start) or at(z1, first->end) <= k;
        have k < at(z2, second->start) or at(z2, second->end) <= k;
        have k < second->arena->capacity by {
            close();
        }
        have second->arena->occupied[k] == at(w2, second->arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < second->arena->capacity implies second->arena->occupied[j] == at(w2, second->arena->occupied[j]) }, k);
            close();
        }
        have at(w2, second->arena->occupied[k]) == at(w2, arena->occupied[k]) by {
            close();
        }
        have k < at(w2, arena->capacity) by {
            normalize() using {
                k < arena->capacity;
                arena->capacity == at(w2, arena->capacity);
            };
        }
        have at(w2, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(w2, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(w2, arena->occupied[j]) == 0 }, k);
            close();
        }
        normalize() using {
            second->arena->occupied[k] == at(w2, second->arena->occupied[k]);
            at(w2, second->arena->occupied[k]) == at(w2, arena->occupied[k]);
            at(w2, arena->occupied[k]) == 0;
            second->arena == arena;
        };
    }
    have first->arena == arena by {
        close();
    }
    have s0.capacity == at(w2, s0.capacity) by {
        close();
    }
    have r1.end <= s0.capacity by {
        close();
    }
    have first->arena->data == second->arena->data by {
        close();
    }
    have at(w2, first->arena->data[(first->start + 0)]) == 11 by {
        close();
    }
    have first->start == at(w2, first->start) by {
        close();
    }
    have second->arena->data == at(w2, second->arena->data) by {
        close();
    }
    have at(w2, second->arena->data) == at(w2, first->arena->data) by {
        close();
    }
    have first->arena->data == at(w2, first->arena->data) by {
        close();
    }
    have &first->arena->data[first->start + 0] == at(w2, &first->arena->data[first->start + 0]) by {
        normalize() using {
            first->arena->data == at(w2, first->arena->data);
            first->start == at(w2, first->start);
        };
    }
    let { live: framed_live, capacity: framed_capacity } = unfold(s0);
    have at(region(25).entry, separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity]))) by close();
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity])) by {
        have arena->occupied == at(region(25).entry, arena->occupied) by close();
        have arena->data == at(region(25).entry, arena->data) by close();
        rewrite(arena->occupied, at(region(25).entry, arena->occupied));
        rewrite(arena->data, at(region(25).entry, arena->data));
        close();
    }
    have separate(memory(*arena), memory(arena->data[0..arena->capacity])) by {
        have arena->data == at(region(25).entry, arena->data) by close();
        rewrite(arena->data, at(region(25).entry, arena->data));
        close();
    }
    have separate(memory(*arena), memory(arena->occupied[0..arena->capacity])) by {
        have arena->occupied == at(region(25).entry, arena->occupied) by close();
        rewrite(arena->occupied, at(region(25).entry, arena->occupied));
        close();
    }
    let { start: framed_start, end: framed_end } = unfold(r1);
    let r1 = fold(arena_region(first), { start: framed_start, end: framed_end });
    let s0 = fold(arena_state(arena), { live: framed_live, capacity: framed_capacity });
    have r1.start == first->start by {
        close();
    }
    have first->start < r1.end by {
        normalize() using { r1.start == first->start; r1.start < r1.end; };
    }
    have (r1.start as int32) <= ((first->start + 0) as int32) by {
        rewrite(first->start, r1.start);
        close();
    }
    have ((first->start + 0) as int32) < (r1.end as int32) by {
        rewrite(first->start, r1.start);
        close() using { r1.start < r1.end; };
    }
    have contains(memory(at(w2_open, arena->data)[at(w2, first->start) + 0]), memory(at(w2_open, arena->data)[at(w2, first->start) + 0])) by { apply(separation::contains_refl(memory(at(w2_open, arena->data)[at(w2, first->start) + 0]))); }
    have separate(statement(12).footprint, memory(at(w2_open, arena->data)[at(w2, first->start) + 0])) by {
        apply(separation::separate_restrict(at(w2, r2) * at(w2, s0), memory(at(w2_open, arena->data)[at(w2, first->start) + 0]), statement(12).footprint, memory(at(w2_open, arena->data)[at(w2, first->start) + 0])));
    }
    have at(w2_open, arena->data)[at(w2, first->start) + 0] == at(w2, at(w2_open, arena->data)[first->start + 0]) by { close(); }
    have at(w2, first->arena->data) == at(w2_open, arena->data) by { close(); }
    have first->arena->data == at(w2_open, arena->data) by {
        rewrite(first->arena->data, at(w2, first->arena->data));
        close();
    }
    have at(statement(12).exit, (let data: int32* = at(w2_open, arena->data); data[at(w2, first->start) + 0]))
        == at(statement(12).entry, (let data: int32* = at(w2_open, arena->data); data[at(w2, first->start) + 0])) by {
        preserve(memory(at(w2_open, arena->data)[at(w2, first->start) + 0]), statement(12));
    }
    have first->arena->data[(first->start + 0)] == at(w2, first->arena->data[(first->start + 0)]) by {
        rewrite(first->arena->data, at(w2_open, arena->data));
        rewrite(first->start, at(w2, first->start));
        close();
    }
    have first->arena->data[(first->start + 0)] == 11 by {
        rewrite(first->arena->data[(first->start + 0)], at(w2, first->arena->data[(first->start +
                0)])); close();
    }
    have second->arena->data[(second->start + 0)] == 22 by {
        close();
    }
    mark m3;
    let { live: kept_live, capacity: kept_capacity } = unfold(s0);
    let { start: kept_start, end: kept_end } = unfold(r2);
    have ((second->start + 0) as int32) == (kept_start as int32) by {
        rewrite(second->start, kept_start);
        close();
    }
    have second->arena->data[kept_start] == 22 by {
        rewrite((kept_start as int32), ((second->start + 0) as int32));
        close();
    }
    let kept = fold(preserved_cell((second->arena->data + kept_start)), { value: 22 });
    let s0 = fold(arena_state(arena), { live: kept_live, capacity: kept_capacity });
    step(arena_read, { r: r1, st: s0 });
    step();
    let { live: returned_live, capacity: returned_capacity } = unfold(s0);
    have at(region(27).entry, separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity]))) by close();
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity])) by {
        have arena->occupied == at(region(27).entry, arena->occupied) by close();
        have arena->data == at(region(27).entry, arena->data) by close();
        rewrite(arena->occupied, at(region(27).entry, arena->occupied));
        rewrite(arena->data, at(region(27).entry, arena->data));
        close();
    }
    have separate(memory(*arena), memory(arena->data[0..arena->capacity])) by {
        have arena->data == at(region(27).entry, arena->data) by close();
        rewrite(arena->data, at(region(27).entry, arena->data));
        close();
    }
    have separate(memory(*arena), memory(arena->occupied[0..arena->capacity])) by {
        have arena->occupied == at(region(27).entry, arena->occupied) by close();
        rewrite(arena->occupied, at(region(27).entry, arena->occupied));
        close();
    }
    let {  } = unfold(kept);
    let s0 = fold(arena_state(arena), { live: returned_live, capacity: returned_capacity });
    have r1.start == at(m3, r1.start) by {
        close();
    }
    have at(m3, r1.start) == at(z1, first->start) by {
        close();
    }
    have r1.start == at(z1, first->start) by {
        rewrite(r1.start, at(m3, r1.start)); close();
    }
    have r1.end == at(m3, r1.end) by {
        close();
    }
    have at(m3, r1.end) == at(z1, first->end) by {
        close();
    }
    have r1.end == at(z1, first->end) by {
        rewrite(r1.end, at(m3, r1.end)); close();
    }
    have s0.live == at(m3, s0.live) by {
        close();
    }
    have at(m3, s0.live) == 2 by {
        close();
    }
    have s0.live == 2 by {
        rewrite(s0.live, at(m3, s0.live)); close();
    }
    have kept_start == at(m3, kept_start) by {
        close();
    }
    have at(m3, kept_start) == at(z2, second->start) by {
        close();
    }
    have kept_start == at(z2, second->start) by {
        rewrite(kept_start, at(m3, kept_start)); close();
    }
    have kept_end == at(m3, kept_end) by {
        close();
    }
    have at(m3, kept_end) == at(z2, second->end) by {
        close();
    }
    have kept_end == at(z2, second->end) by {
        rewrite(kept_end, at(m3, kept_end)); close();
    }
    have first_value == 11 by {
        close();
    }
    have first->arena == arena by {
        rewrite(first->arena, at(m3, first->arena)); close();
    }
    have first->arena->capacity == at(m3, first->arena->capacity) by {
        close();
    }
    have arena->capacity == first->arena->capacity by {
        close();
    }
    have at(m3, first->arena->capacity) == at(m3, arena->capacity) by {
        close();
    }
    have arena->capacity == at(m3, arena->capacity) by {
        normalize() using {
            arena->capacity == first->arena->capacity;
            first->arena->capacity == at(m3, first->arena->capacity);
            at(m3, first->arena->capacity) == at(m3, arena->capacity);
        };
    }
    have s0.capacity == at(m3, s0.capacity) by {
        close();
    }
    have s0.capacity == arena->capacity by {
        close();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) and (k < at(z2, second->start) or at(z2, second->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        have k < at(z1, first->start) or at(z1, first->end) <= k;
        have k < at(z2, second->start) or at(z2, second->end) <= k;
        have k < first->arena->capacity by {
            close();
        }
        have first->arena->occupied[k] == at(m3, first->arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < first->arena->capacity implies first->arena->occupied[j] == at(m3, first->arena->occupied[j]) }, k);
            close();
        }
        have at(m3, first->arena->occupied[k]) == at(m3, arena->occupied[k]) by {
            normalize() using {
                at(m3, first->arena) == arena;
            };
        }
        have k < at(m3, arena->capacity) by {
            normalize() using {
                k < arena->capacity;
                arena->capacity == at(m3, arena->capacity);
            };
        }
        have at(m3, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(m3, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(m3, arena->occupied[j]) == 0 }, k);
            close();
        }
        normalize() using {
            first->arena->occupied[k] == at(m3, first->arena->occupied[k]);
            at(m3, first->arena->occupied[k]) == at(m3, arena->occupied[k]);
            at(m3, arena->occupied[k]) == 0;
            first->arena == arena;
        };
    }
    have second->arena == arena by {
        close();
    }
    have second->start == at(m3, second->start) by {
        close();
    }
    have first->arena->data == at(m3, first->arena->data) by {
        close();
    }
    have second->arena->data == first->arena->data by {
        close();
    }
    have at(m3, first->arena->data) == at(m3, second->arena->data) by {
        close();
    }
    have second->arena->data == at(m3, second->arena->data) by {
        close();
    }
    have &second->arena->data[second->start + 0] == (at(m3, second->arena->data) + kept_start) by {
        normalize() using {
            second->arena->data == at(m3, second->arena->data);
            second->start == at(m3, second->start);
            at(m3, second->start) == kept_start;
        };
    }
    have second->arena->data[(second->start + 0)] == 22 by {
        rewrite(&second->arena->data[second->start + 0], (at(m3, second->arena->data) + kept_start));
        close();
    }
    have (at(m3, second->arena->data) + at(m3, second->start)) == (second->arena->data + kept_start) by {
        normalize() using {
            second->arena->data == at(m3, second->arena->data);
            at(m3, second->start) == kept_start;
        };
    }
    have (at(m3, second->arena->data) + (at(m3, second->start) + 1)) == (second->arena->data + (kept_start + 1)) by {
        normalize() using {
            second->arena->data == at(m3, second->arena->data);
            at(m3, second->start) == kept_start;
        };
    }
    let r2 = fold(arena_region(second), { start: kept_start, end: kept_end });
    have r2.end <= s0.capacity by {
        close();
    }
    let { live: m4_live, capacity: m4_capacity } = unfold(s0);
    let { start: m4_start, end: m4_end } = unfold(r1);
    let s0 = fold(arena_state(arena), { live: m4_live, capacity: m4_capacity });
    have separate(r2, memory(*first)) by { close(); }
    have separate(s0, memory(*first)) by { close(); }
    have separate(r2 * s0, memory(*first)) by {
        apply(separation::separate_star(r2, s0, memory(*first)));
    }
    let r1 = fold(arena_region(first), { start: m4_start, end: m4_end });
    mark m4;
    step(arena_read, { r: r2, st: s0 });
    have contains(at(m4, r2) * at(m4, s0), statement(14).call(0).footprint) by { close(); }
    have contains(memory(*first), memory(first->arena)) by { close(); }
    have separate(statement(14).call(0).footprint, memory(first->arena)) by {
        apply(separation::separate_restrict(at(m4, r2) * at(m4, s0), memory(*first), statement(14).call(0).footprint, memory(first->arena)));
    }
    have first->arena == at(m4, first->arena) by {
        preserve(memory(first->arena), statement(14).call(0));
    }
    step();
    have r1.start == at(m4, r1.start) by {
        close();
    }
    have at(m4, r1.start) == at(z1, first->start) by {
        close();
    }
    have r1.start == at(z1, first->start) by {
        rewrite(r1.start, at(m4, r1.start)); close();
    }
    have r1.end == at(m4, r1.end) by {
        close();
    }
    have at(m4, r1.end) == at(z1, first->end) by {
        close();
    }
    have r1.end == at(z1, first->end) by {
        rewrite(r1.end, at(m4, r1.end)); close();
    }
    have s0.live == at(m4, s0.live) by {
        close();
    }
    have at(m4, s0.live) == 2 by {
        close();
    }
    have s0.live == 2 by {
        rewrite(s0.live, at(m4, s0.live)); close();
    }
    have r2.start == at(m4, r2.start) by {
        close();
    }
    have at(m4, r2.start) == at(z2, second->start) by {
        close();
    }
    have r2.start == at(z2, second->start) by {
        rewrite(r2.start, at(m4, r2.start)); close();
    }
    have r2.end == at(m4, r2.end) by {
        close();
    }
    have at(m4, r2.end) == at(z2, second->end) by {
        close();
    }
    have r2.end == at(z2, second->end) by {
        rewrite(r2.end, at(m4, r2.end)); close();
    }
    have second_value == 22 by {
        close();
    }
    have first_value == 11 by {
        close();
    }
    step();
    have value == 33 by {
        close();
    }
    have second->arena == arena by {
        close();
    }
    have second->arena->capacity == at(m4, second->arena->capacity) by {
        close();
    }
    have arena->capacity == second->arena->capacity by {
        close();
    }
    have at(m4, second->arena->capacity) == at(m4, arena->capacity) by {
        normalize() using {
            at(m4, second->arena) == arena;
        };
    }
    have arena->capacity == at(m4, arena->capacity) by {
        normalize() using {
            arena->capacity == second->arena->capacity;
            second->arena->capacity == at(m4, second->arena->capacity);
            at(m4, second->arena->capacity) == at(m4, arena->capacity);
        };
    }
    have s0.capacity == at(m4, s0.capacity) by {
        close();
    }
    have s0.capacity == arena->capacity by {
        close();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) and (k < at(z2, second->start) or at(z2, second->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        have k < at(z1, first->start) or at(z1, first->end) <= k;
        have k < at(z2, second->start) or at(z2, second->end) <= k;
        have k < second->arena->capacity by {
            normalize() using {
                k < arena->capacity;
                second->arena == arena;
            };
        }
        have second->arena->occupied[k] == at(m4, second->arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < second->arena->capacity implies second->arena->occupied[j] == at(m4, second->arena->occupied[j]) }, k);
            close();
        }
        have at(m4, second->arena->occupied[k]) == at(m4, arena->occupied[k]) by {
            normalize() using {
                at(m4, second->arena) == arena;
            };
        }
        have k < at(m4, arena->capacity) by {
            normalize() using {
                k < arena->capacity;
                arena->capacity == at(m4, arena->capacity);
            };
        }
        have at(m4, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(m4, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(m4, arena->occupied[j]) == 0 }, k);
            close();
        }
        normalize() using {
            second->arena->occupied[k] == at(m4, second->arena->occupied[k]);
            at(m4, second->arena->occupied[k]) == at(m4, arena->occupied[k]);
            at(m4, arena->occupied[k]) == 0;
            second->arena == arena;
        };
    }
    have s0.live == 2 by {
        close();
    }
    have 1 <= s0.live by {
        close() using { (at(region(30).entry, s0.live) as int32) == (at(region(30).entry, 2) as
                int32); };
    }
    have r2.end <= s0.capacity by {
        close();
    }
    have s0.capacity == arena->capacity by {
        close();
    }
    have r1.end <= s0.capacity by {
        have r1.end == at(m4, r1.end) by {
            close();
        }
        have s0.capacity == at(m4, s0.capacity) by {
            close();
        }
        have at(m4, r1.end) <= at(m4, s0.capacity) by {
            close();
        }
        close();
    }
    have first->arena == arena by { close(); }
    let { live: f2_live, capacity: f2_capacity } = unfold(s0);
    let { start: f2_start, end: f2_end } = unfold(r1);
    let s0 = fold(arena_state(arena), { live: f2_live, capacity: f2_capacity });
    have separate(r2, memory(*first)) by { close(); }
    have separate(s0, memory(*first)) by { close(); }
    have separate(r2 * s0, memory(*first)) by {
        apply(separation::separate_star(r2, s0, memory(*first)));
    }
    let r1 = fold(arena_region(first), { start: f2_start, end: f2_end });
    mark f2;
    let { after: g2 } = step(arena_free, { r: r2, st: s0 });
    have contains(at(f2, r2) * at(f2, s0), statement(16).footprint) by { close(); }
    have contains(memory(*first), memory(first->arena)) by { close(); }
    have separate(statement(16).footprint, memory(first->arena)) by {
        apply(separation::separate_restrict(at(f2, r2) * at(f2, s0), memory(*first), statement(16).footprint, memory(first->arena)));
    }
    have first->arena == at(f2, first->arena) by {
        preserve(memory(first->arena), statement(16));
    }
    have r1.start == at(f2, r1.start) by {
        close();
    }
    have at(f2, r1.start) == at(z1, first->start) by {
        close();
    }
    have r1.start == at(z1, first->start) by {
        rewrite(r1.start, at(f2, r1.start)); close();
    }
    have r1.end == at(f2, r1.end) by {
        close();
    }
    have at(f2, r1.end) == at(z1, first->end) by {
        close();
    }
    have r1.end == at(z1, first->end) by {
        rewrite(r1.end, at(f2, r1.end)); close();
    }
    have second->arena == arena by {
        close();
    }
    have second->arena->capacity == at(f2, second->arena->capacity) by {
        close();
    }
    have arena->capacity == second->arena->capacity by {
        close();
    }
    have at(f2, second->arena->capacity) == at(f2, arena->capacity) by {
        normalize() using {
            at(f2, second->arena) == arena;
        };
    }
    have arena->capacity == at(f2, arena->capacity) by {
        normalize() using {
            arena->capacity == second->arena->capacity;
            second->arena->capacity == at(f2, second->arena->capacity);
            at(f2, second->arena->capacity) == at(f2, arena->capacity);
        };
    }
    have second->start == at(f2, r2.start) by {
        close();
    }
    have at(f2, r2.start) == at(z2, second->start) by {
        close();
    }
    have second->start == at(z2, second->start) by {
        rewrite(second->start, at(f2, r2.start)); close();
    }
    have second->end == at(f2, r2.end) by {
        close();
    }
    have at(f2, r2.end) == at(z2, second->end) by {
        close();
    }
    have second->end == at(z2, second->end) by {
        rewrite(second->end, at(f2, r2.end)); close();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        have k < at(z1, first->start) or at(z1, first->end) <= k;
        have k < second->start implies arena->occupied[k] == 0 by {
            intro();
            have second->arena->occupied[k] == at(f2, second->arena->occupied[k]) by {
                instantiate(forall (j: int32) { 0 <= j and j < second->start implies second->arena->occupied[j] == at(f2, second->arena->occupied[j]) }, k);
                close();
            }
            have at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]) by {
                normalize() using {
                    at(f2, second->arena) == arena;
                };
            }
            have k < at(f2, arena->capacity) by {
                normalize() using {
                    k < arena->capacity;
                    arena->capacity == at(f2, arena->capacity);
                };
            }
            have k < at(z2, second->start) by {
                close();
            }
            have k < at(z2, second->start) or at(z2, second->end) <= k by {
                close();
            }
            have at(f2, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(f2, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(f2, arena->occupied[j]) == 0 }, k);
                close();
            }
            normalize() using {
                second->arena->occupied[k] == at(f2, second->arena->occupied[k]);
                at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]);
                at(f2, arena->occupied[k]) == 0;
                second->arena == arena;
            };
        }
        have second->start <= k and k < second->end implies arena->occupied[k] == 0 by {
            intro();
            have second->start <= k;
            have k < second->end;
            have arena->occupied[k] == 0 by {
                instantiate(forall (j: int32) { second->start <= j and j < second->end implies second->arena->occupied[j] == 0 }, k);
                normalize() using {
                    second->arena->occupied[k] == 0;
                    second->arena == arena;
                };
            }
            close();
        }
        have second->end <= k implies arena->occupied[k] == 0 by {
            intro();
            have k < second->arena->capacity by {
                normalize() using {
                    k < arena->capacity;
                    second->arena == arena;
                };
            }
            have second->arena->occupied[k] == at(f2, second->arena->occupied[k]) by {
                instantiate(forall (j: int32) { second->end <= j and j < second->arena->capacity implies second->arena->occupied[j] == at(f2, second->arena->occupied[j]) }, k);
                close();
            }
            have at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]) by {
                normalize() using {
                    at(f2, second->arena) == arena;
                };
            }
            have k < at(f2, arena->capacity) by {
                normalize() using {
                    k < arena->capacity;
                    arena->capacity == at(f2, arena->capacity);
                };
            }
            have at(z2, second->end) <= k by {
                normalize() using {
                    second->end <= k;
                    second->end == at(z2, second->end);
                };
            }
            have k < at(z2, second->start) or at(z2, second->end) <= k by {
                close();
            }
            have at(f2, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(f2, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(f2, arena->occupied[j]) == 0 }, k);
                close();
            }
            normalize() using {
                second->arena->occupied[k] == at(f2, second->arena->occupied[k]);
                at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]);
                at(f2, arena->occupied[k]) == 0;
                second->arena == arena;
            };
        }
        if k < second->start {
            have k < second->start by {
                close();
            }
            have arena->occupied[k] == 0; close();
        } else {
            have second->start <= k by {
                close();
            }
            if k < second->end {
                have second->start <= k and k < second->end by {
                    close();
                }
                have arena->occupied[k] == 0; close();
            } else {
                have second->end <= k by {
                    close();
                }
                have arena->occupied[k] == 0; close();
            }
        }
    }
    have g2.live == 1 by {
        close();
    }
    have 1 <= g2.live by {
        close() using { (at(region(31).entry, g2.live) as int32) == (at(region(31).entry, 1) as
                int32); };
    }
    have g2.capacity == at(f2, s0.capacity) by {
        close();
    }
    have at(f2, s0.capacity) == at(f2, arena->capacity) by {
        close();
    }
    have g2.capacity == arena->capacity by {
        close();
    }
    have r1.end <= g2.capacity by {
        have r1.end == at(f2, r1.end) by {
            close();
        }
        have at(f2, r1.end) <= at(f2, s0.capacity) by {
            close();
        }
        close();
    }
    have first->arena == arena by {
        close();
    }
    mark f3;
    let { after: g3 } = step(arena_free, { r: r1, st: g2 });
    have first->arena == arena by {
        rewrite(first->arena, at(f3, first->arena)); close();
    }
    have first->arena->capacity == at(f3, first->arena->capacity) by {
        close();
    }
    have arena->capacity == first->arena->capacity by {
        close();
    }
    have at(f3, first->arena->capacity) == at(f3, arena->capacity) by {
        close();
    }
    have arena->capacity == at(f3, arena->capacity) by {
        normalize() using {
            arena->capacity == first->arena->capacity;
            first->arena->capacity == at(f3, first->arena->capacity);
            at(f3, first->arena->capacity) == at(f3, arena->capacity);
        };
    }
    have first->start == at(f3, r1.start) by {
        close();
    }
    have at(f3, r1.start) == at(z1, first->start) by {
        close();
    }
    have first->start == at(z1, first->start) by {
        rewrite(first->start, at(f3, r1.start)); close();
    }
    have first->end == at(f3, r1.end) by {
        close();
    }
    have at(f3, r1.end) == at(z1, first->end) by {
        close();
    }
    have first->end == at(z1, first->end) by {
        rewrite(first->end, at(f3, r1.end)); close();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        have 0 <= k;
        have k < arena->capacity;
        have k < first->start implies arena->occupied[k] == 0 by {
            intro();
            have first->arena->occupied[k] == at(f3, first->arena->occupied[k]) by {
                instantiate(forall (j: int32) { 0 <= j and j < first->start implies first->arena->occupied[j] == at(f3, first->arena->occupied[j]) }, k);
                close();
            }
            have at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]) by {
                normalize() using {
                    at(f3, first->arena) == arena;
                };
            }
            have k < at(f3, arena->capacity) by {
                close();
            }
            have k < at(z1, first->start) by {
                close();
            }
            have k < at(z1, first->start) or at(z1, first->end) <= k by {
                close();
            }
            have at(f3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(f3, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(f3, arena->occupied[j]) == 0 }, k);
                close();
            }
            normalize() using {
                first->arena->occupied[k] == at(f3, first->arena->occupied[k]);
                at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]);
                at(f3, arena->occupied[k]) == 0;
                first->arena == arena;
            };
        }
        have first->start <= k and k < first->end implies arena->occupied[k] == 0 by {
            intro();
            have first->start <= k;
            have k < first->end;
            have arena->occupied[k] == 0 by {
                instantiate(forall (j: int32) { first->start <= j and j < first->end implies first->arena->occupied[j] == 0 }, k);
                normalize() using {
                    first->arena->occupied[k] == 0;
                    first->arena == arena;
                };
            }
            close();
        }
        have first->end <= k implies arena->occupied[k] == 0 by {
            intro();
            have k < first->arena->capacity by {
                close();
            }
            have first->arena->occupied[k] == at(f3, first->arena->occupied[k]) by {
                instantiate(forall (j: int32) { first->end <= j and j < first->arena->capacity implies first->arena->occupied[j] == at(f3, first->arena->occupied[j]) }, k);
                close();
            }
            have at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]) by {
                normalize() using {
                    at(f3, first->arena) == arena;
                };
            }
            have k < at(f3, arena->capacity) by {
                close();
            }
            have at(z1, first->end) <= k by {
                close();
            }
            have k < at(z1, first->start) or at(z1, first->end) <= k by {
                close();
            }
            have at(f3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(f3, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(f3, arena->occupied[j]) == 0 }, k);
                close();
            }
            normalize() using {
                first->arena->occupied[k] == at(f3, first->arena->occupied[k]);
                at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]);
                at(f3, arena->occupied[k]) == 0;
                first->arena == arena;
            };
        }
        if k < first->start {
            have k < first->start by {
                close();
            }
            have arena->occupied[k] == 0; close();
        } else {
            have first->start <= k by {
                close();
            }
            if k < first->end {
                have first->start <= k and k < first->end by {
                    close();
                }
                have arena->occupied[k] == 0; close();
            } else {
                have first->end <= k by {
                    close();
                }
                have arena->occupied[k] == 0; close();
            }
        }
    }
    have g3.live == 0 by {
        close();
    }
    have g3.live < 2147483647 by {
        normalize() using {
            g3.live == 0;
        };
    }
    mark a3;
    let { outcome: o3 } = step(arena_alloc, { st: g3 });
    mark after_combined_alloc;
    step();
    have separate(memory(allocated), memory(combined->arena)) by { close(); }
    have separate(statement(18).assignment(allocated, 0).footprint, memory(combined->arena)) by {
        normalize() using { separate(memory(allocated), memory(combined->arena)); };
    }
    have combined->arena == at(after_combined_alloc, combined->arena) by {
        preserve(memory(combined->arena), statement(18).assignment(allocated, 0));
    }
    have allocated == 1 implies combined->arena == arena by {
        intro();
        have at(after_combined_alloc, combined->arena) == arena;
        close();
    }
    have arena->capacity == at(a3, arena->capacity) by {
        close();
    }
    if at(region(34).entry, allocated) == at(region(34).entry, 0) {
        step();
        have o3.model == ArenaAllocOutcome::Failure() by close();
        have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            have arena->occupied[k] == at(a3, arena->occupied[k]) by {
                instantiate(forall (j: int32) { allocated == 0 and 0 <= j and j < arena->capacity implies arena->occupied[j] == at(a3, arena->occupied[j]) }, k);
                close();
            }
            have k < at(a3, arena->capacity) by {
                close();
            }
            have at(a3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(a3, arena->capacity) implies at(a3, arena->occupied[j]) == 0 }, k);
                close();
            }
            normalize() using {
                arena->occupied[k] == at(a3, arena->occupied[k]);
                at(a3, arena->occupied[k]) == 0;
            };
        }
        step(arena_destroy, { st: g3 });
        unfold(o3);
        step();
        close();
        have result == 0 or result == 33 by {
            close();
        }
        close();
        close();
        close();
        close();
    } else {
        step();
        step();
        have allocated == 1 by {
            cases {
                allocated == 0 => {
                    contradiction(allocated == 0);
                }
                allocated == 1 => {
                    close();
                }
            }
        }
        have o3.model == ArenaAllocOutcome::Success(combined->start, combined->end) by close();
        have 0 <= combined->start by close();
        have combined->start < combined->end by close();
        have combined->end <= arena->capacity by close();
        have arena->capacity <= 536870911 by {
            close();
        }
        have combined->start < 536870911 by {
            close() using { at(region(38).entry, combined->end) <= at(region(38).entry,
                    arena->capacity); at(region(38).entry, arena->capacity) <= at(region(38).entry, 536870911); at(region(38).entry, combined->start) < at(region(38).entry,
                    combined->end); };
        }
        have g3.live == 1 by {
            close();
        }
        let { allocated: r3 } = unfold(o3);
        mark z3;
        have r3.start == at(z3, combined->start) by {
            close();
        }
        have r3.end == at(z3, combined->end) by {
            close();
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z3, combined->start) or at(z3, combined->end) <= k) implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            have k < at(z3, combined->start) or at(z3, combined->end) <= k;
            have k < at(a3, arena->capacity) by {
                close();
            }
            have at(a3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(a3, arena->capacity) implies at(a3, arena->occupied[j]) == 0 }, k);
                close();
            }
            cases {
                k < at(z3, combined->start) => {
                    have k < combined->start by {
                        close();
                    }
                    have arena->occupied[k] == at(a3, arena->occupied[k]) by {
                        instantiate(forall (j: int32) { allocated == 1 and 0 <= j and j < combined->start implies arena->occupied[j] == at(a3, arena->occupied[j]) }, k);
                        close();
                    }
                    rewrite(arena->occupied[k], at(a3, arena->occupied[k]));
                    rewrite(at(a3, arena->occupied[k]), 0);
                    close();
                }
                at(z3, combined->end) <= k => {
                    have combined->end <= k by {
                        close();
                    }
                    have arena->occupied[k] == at(a3, arena->occupied[k]) by {
                        instantiate(forall (j: int32) { allocated == 1 and combined->end <= j and j < arena->capacity implies arena->occupied[j] == at(a3, arena->occupied[j]) }, k);
                        close();
                    }
                    normalize() using {
                        arena->occupied[k] == at(a3, arena->occupied[k]);
                        at(a3, arena->occupied[k]) == 0;
                    };
                }
            }
        }
        have combined->arena == arena by close();
        have g3.capacity == arena->capacity by {
            close();
        }
        have 0 <= r3.start by {
            close();
        }
        have r3.start < 536870911 by {
            close();
        }
        have r3.start < 2147483643 by {
            close() using { at(region(38).entry, combined->start) < at(region(38).entry, 536870911); };
        }
        have r3.start <= 2147483643 by {
            close() using { (at(region(38).entry, combined->start) as int32) < (at(region(38).entry,
                    536870911) as int32); };
        }
        have defined((r3.start + 4)) by {
            have (to_integer(r3.start) + to_integer(4)) >= -2147483648 by {
                close() using { 0 <= to_integer(r3.start); };
            }
            have (to_integer(r3.start) + to_integer(4)) <= 2147483647 by {
                close() using { to_integer(r3.start) < 536870911; };
            }
            close();
        }
        have at(z3, combined->start) == r3.start by {
            close();
        }
        have to_integer((at(z3, combined->start) + 4)) == (to_integer(at(z3, combined->start)) + 4) by {
            have -2147483648 <= (to_integer(at(z3, combined->start)) + 4) by {
                close();
            }
            have (to_integer(at(z3, combined->start)) + 4) <= 2147483647 by {
                close();
            }
            have to_integer((at(z3, combined->start) + 4)) == (to_integer(at(z3, combined->start)) + 4) by {
                close() using { -2147483648 <= (to_integer(at(z3, combined->start)) + 4); (to_integer(at(z3, combined->start)) + 4) <= 2147483647; };
            }
            close();
        }
        have to_integer(at(z3, combined->end)) == to_integer((at(z3, combined->start) + 4)) by {
            rewrite(to_integer((at(z3, combined->start) + 4)), (to_integer(at(z3, combined->start)) + 4));
            have to_integer(at(z3, combined->end)) == (to_integer(at(z3, combined->start)) + 4); close();
        }
        have to_integer(at(z3, combined->end)) == (to_integer(at(z3, combined->start)) + 4) by {
            rewrite(to_integer(at(z3, combined->end)), to_integer((at(z3, combined->start) + 4))); close();
        }
        have to_integer(r3.end) == (to_integer(r3.start) + 4) by {
            normalize() using {
                r3.start == at(z3, combined->start);
                r3.end == at(z3, combined->end);
                to_integer(at(z3, combined->end)) == (to_integer(at(z3, combined->start)) + 4);
            };
        }
        have r3.end <= g3.capacity by {
            close();
        }
        have r3.start <= 2147483644 by {
            close() using { (at(region(38).entry, combined->start) as int32) < (at(region(38).entry,
                    536870911) as int32); };
        }
        have defined((r3.start + 3)) by {
            have (to_integer(r3.start) + to_integer(3)) >= -2147483648 by {
                close() using { 0 <= to_integer(r3.start); };
            }
            have (to_integer(r3.start) + to_integer(3)) <= 2147483647 by {
                close() using { (let integer_value: Integer = to_integer((combined->start as int32))
                        + 4; integer_value) <= 2147483647; };
            }
            close();
        }
        have (to_integer(r3.start) + 3) < to_integer(r3.end) by {
            rewrite(to_integer(at(z3, combined->end)), (to_integer(at(z3, combined->start)) + 4));
            close();
        }
        have value == 33 by {
            close();
        }
        mark w3;
        step(arena_write, { r: r3, st: g3 });
        have r3.start == at(w3, r3.start) by {
            close();
        }
        have defined((r3.start + 3)) by {
            close();
        }
        have combined->arena->data[(r3.start + 3)] == value by {
            close();
        }
        have combined->arena == arena by {
            close();
        }
        have combined->arena->capacity == at(w3, combined->arena->capacity) by {
            close();
        }
        have arena->capacity == combined->arena->capacity by {
            close();
        }
        have at(w3, combined->arena->capacity) == at(w3, arena->capacity) by {
            close();
        }
        have arena->capacity == at(w3, arena->capacity) by {
            close();
        }
        have g3.capacity == at(w3, g3.capacity) by {
            close();
        }
        have g3.capacity == arena->capacity by {
            close();
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z3, combined->start) or at(z3, combined->end) <= k) implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            have k < at(z3, combined->start) or at(z3, combined->end) <= k;
            have k < combined->arena->capacity by {
                close();
            }
            have combined->arena->occupied[k] == at(w3, combined->arena->occupied[k]) by {
                instantiate(forall (j: int32) { 0 <= j and j < combined->arena->capacity implies combined->arena->occupied[j] == at(w3, combined->arena->occupied[j]) }, k);
                close();
            }
            have at(w3, combined->arena->occupied[k]) == at(w3, arena->occupied[k]) by {
                close();
            }
            have k < at(w3, arena->capacity) by {
                close();
            }
            have at(w3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(w3, arena->capacity) and (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies at(w3, arena->occupied[j]) == 0 }, k);
                close();
            }
            normalize() using {
                combined->arena->occupied[k] == at(w3, combined->arena->occupied[k]);
                at(w3, combined->arena->occupied[k]) == at(w3, arena->occupied[k]);
                at(w3, arena->occupied[k]) == 0;
                combined->arena == arena;
            };
        }
        have g3.live == at(w3, g3.live) by {
            close();
        }
        have g3.live == 1 by {
            close();
        }
        have r3.start == at(w3, r3.start) by {
            close();
        }
        have r3.end == at(w3, r3.end) by {
            close();
        }
        have r3.start == at(z3, combined->start) by {
            close();
        }
        have r3.end == at(z3, combined->end) by {
            close();
        }
        have r3.end <= g3.capacity by {
            have r3.end <= at(w3, g3.capacity) by {
                close();
            }
            normalize() using {
                r3.end <= at(w3, g3.capacity);
                g3.capacity == at(w3, g3.capacity);
            };
        }
        have defined((r3.start + 3)) by {
            close();
        }
        have (to_integer(r3.start) + 3) < to_integer(r3.end) by {
            close();
        }
        have combined->arena->data[(r3.start + 3)] == 33 by {
            close();
        }
        mark m5;
        step(arena_read, { r: r3, st: g3 });
        step();
        have value == at(m5, combined->arena->data[(r3.start + 3)]) by {
            close();
        }
        have value == 33 by {
            close();
        }
        have combined->arena == arena by {
            close();
        }
        have combined->arena->capacity == at(m5, combined->arena->capacity) by {
            close();
        }
        have arena->capacity == combined->arena->capacity by {
            close();
        }
        have at(m5, combined->arena->capacity) == at(m5, arena->capacity) by {
            close();
        }
        have arena->capacity == at(m5, arena->capacity) by {
            close();
        }
        have g3.capacity == at(m5, g3.capacity) by {
            close();
        }
        have g3.capacity == arena->capacity by {
            close();
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z3, combined->start) or at(z3, combined->end) <= k) implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            have k < at(z3, combined->start) or at(z3, combined->end) <= k;
            have k < combined->arena->capacity by {
                close();
            }
            have combined->arena->occupied[k] == at(m5, combined->arena->occupied[k]) by {
                instantiate(forall (j: int32) { 0 <= j and j < combined->arena->capacity implies combined->arena->occupied[j] == at(m5, combined->arena->occupied[j]) }, k);
                close();
            }
            have at(m5, combined->arena->occupied[k]) == at(m5, arena->occupied[k]) by {
                close();
            }
            have k < at(m5, arena->capacity) by {
                close();
            }
            have at(m5, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(m5, arena->capacity) and (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies at(m5, arena->occupied[j]) == 0 }, k);
                close();
            }
            normalize() using {
                combined->arena->occupied[k] == at(m5, combined->arena->occupied[k]);
                at(m5, combined->arena->occupied[k]) == at(m5, arena->occupied[k]);
                at(m5, arena->occupied[k]) == 0;
                combined->arena == arena;
            };
        }
        have g3.live == 1 by {
            close();
        }
        have 1 <= g3.live by {
            close();
        }
        have r3.start == at(z3, combined->start) by {
            close();
        }
        have r3.end == at(z3, combined->end) by {
            close();
        }
        have r3.end <= g3.capacity by {
            have r3.end == at(m5, r3.end) by {
                close();
            }
            have r3.end <= at(m5, g3.capacity) by {
                close();
            }
            normalize() using {
                r3.end <= at(m5, g3.capacity);
                g3.capacity == at(m5, g3.capacity);
            };
        }
        mark f4;
        let { after: g4 } = step(arena_free, { r: r3, st: g3 });
        have combined->arena == arena by {
            close();
        }
        have combined->arena->capacity == at(f4, combined->arena->capacity) by {
            close();
        }
        have arena->capacity == combined->arena->capacity by {
            close();
        }
        have at(f4, combined->arena->capacity) == at(f4, arena->capacity) by {
            close();
        }
        have arena->capacity == at(f4, arena->capacity) by {
            close();
        }
        have combined->start == at(z3, combined->start) by {
            close();
        }
        have combined->end == at(z3, combined->end) by {
            close();
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            have 0 <= k;
            have k < arena->capacity;
            have k < combined->start implies arena->occupied[k] == 0 by {
                intro();
                have combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]) by {
                    instantiate(forall (j: int32) { 0 <= j and j < combined->start implies combined->arena->occupied[j] == at(f4, combined->arena->occupied[j]) }, k);
                    close();
                }
                have at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]) by {
                    normalize() using {
                        at(f4, combined->arena) == arena;
                    };
                }
                have k < at(f4, arena->capacity) by {
                    normalize() using {
                        k < arena->capacity;
                        arena->capacity == at(f4, arena->capacity);
                    };
                }
                have k < at(z3, combined->start) by {
                    normalize() using {
                        k < combined->start;
                        combined->start == at(z3, combined->start);
                    };
                }
                have k < at(z3, combined->start) or at(z3, combined->end) <= k by {
                    close();
                }
                have at(f4, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) { 0 <= j and j < at(f4, arena->capacity) and (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies at(f4, arena->occupied[j]) == 0 }, k);
                    close();
                }
                normalize() using {
                    combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]);
                    at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]);
                    at(f4, arena->occupied[k]) == 0;
                    combined->arena == arena;
                };
            }
            have combined->start <= k and k < combined->end implies arena->occupied[k] == 0 by {
                intro();
                have combined->start <= k;
                have k < combined->end;
                have arena->occupied[k] == 0 by {
                    instantiate(forall (j: int32) { combined->start <= j and j < combined->end implies combined->arena->occupied[j] == 0 }, k);
                    normalize() using {
                        combined->arena->occupied[k] == 0;
                        combined->arena == arena;
                    };
                }
                close();
            }
            have combined->end <= k implies arena->occupied[k] == 0 by {
                intro();
                have k < combined->arena->capacity by {
                    normalize() using {
                        k < arena->capacity;
                        combined->arena == arena;
                    };
                }
                have combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]) by {
                    instantiate(forall (j: int32) { combined->end <= j and j < combined->arena->capacity implies combined->arena->occupied[j] == at(f4, combined->arena->occupied[j]) }, k);
                    close();
                }
                have at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]) by {
                    normalize() using {
                        at(f4, combined->arena) == arena;
                    };
                }
                have k < at(f4, arena->capacity) by {
                    normalize() using {
                        k < arena->capacity;
                        arena->capacity == at(f4, arena->capacity);
                    };
                }
                have at(z3, combined->end) <= k by {
                    normalize() using {
                        combined->end <= k;
                        combined->end == at(z3, combined->end);
                    };
                }
                have k < at(z3, combined->start) or at(z3, combined->end) <= k by {
                    close();
                }
                have at(f4, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) { 0 <= j and j < at(f4, arena->capacity) and (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies at(f4, arena->occupied[j]) == 0 }, k);
                    close();
                }
                normalize() using {
                    combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]);
                    at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]);
                    at(f4, arena->occupied[k]) == 0;
                    combined->arena == arena;
                };
            }
            if k < combined->start {
                have k < combined->start by {
                    close();
                }
                have arena->occupied[k] == 0; close();
            } else {
                have combined->start <= k by {
                    close();
                }
                if k < combined->end {
                    have combined->start <= k and k < combined->end by {
                        close();
                    }
                    have arena->occupied[k] == 0; close();
                } else {
                    have combined->end <= k by {
                        close();
                    }
                    have arena->occupied[k] == 0; close();
                }
            }
        }
        step(arena_destroy, { st: g4 });
        step();
        close();
        have result == 0 or result == 33 by {
            close();
        }
        close();
        close();
        close();
        close();
    }
}

verifying "arena_reuse.c";

int32 arena_reuse(struct region* middle, struct region* reused) {
    consumes r: arena_region(middle);
    consumes st: arena_state(middle->arena);
    consumes *reused;
    requires r.start == 2;
    requires r.end == 4;
    requires st.capacity == 6;
    requires 1 <= st.live;
    requires forall (k: int32) {
        0 <= k and k < middle->arena->capacity implies middle->arena->occupied[k] == 1
    };
    produces *middle;
    produces after: arena_state(middle->arena);
    produces outcome: arena_alloc_result(reused);

    ensures result == 1 implies 2 <= reused->start and reused->end <= 4;
} by {
    step();
    let { after: after } = step(arena_free, { r: r, st: st });
    have middle->start == 2;
    have middle->end == 4;
    have after.live == old(st.live) - 1;
    have 0 < old(st.live);
    have old(st.live) - 1 < old(st.live);
    have forall (k: int32) {
        0 <= k and k < middle->arena->capacity implies
            (middle->arena->occupied[k] == 0 implies 2 <= k and k < 4)
    } by {
        intro();
        intro();
        have 0 <= k;
        have k < middle->arena->capacity;
        intro();
        if k < 2 {
            have k < middle->start;
            instantiate(forall (j: int32) {
                0 <= j and j < middle->start implies
                    middle->arena->occupied[j] == old(middle->arena->occupied[j])
            }, k);
            have k < old(middle->arena->capacity);
            instantiate(forall (j: int32) {
                0 <= j and j < old(middle->arena->capacity) implies
                    old(middle->arena->occupied[j]) == 1
            }, k);
            have middle->arena->occupied[k] == 1;
            have not (middle->arena->occupied[k] == 0);
            contradiction(middle->arena->occupied[k] == 0);
        } else {
            if k < 4 {
                have 2 <= k and k < 4;
                close();
            } else {
                have middle->end <= k;
                instantiate(forall (j: int32) {
                    middle->end <= j and j < middle->arena->capacity implies
                        middle->arena->occupied[j] == old(middle->arena->occupied[j])
                }, k);
                have k < old(middle->arena->capacity);
                instantiate(forall (j: int32) {
                    0 <= j and j < old(middle->arena->capacity) implies
                        old(middle->arena->occupied[j]) == 1
                }, k);
                have middle->arena->occupied[k] == 1;
                have not (middle->arena->occupied[k] == 0);
            contradiction(middle->arena->occupied[k] == 0);
            }
        }
    }
    mark allocating;
    let { outcome: outcome } = step(arena_alloc, { st: after });
    step();
    have middle->arena->capacity == at(allocating, middle->arena->capacity);
    have forall (k: int32) {
        allocated == 1 and reused->start <= k and k < reused->end implies 2 <= k and k < 4
    } by {
        intro();
        intro();
        have allocated == 1;
        have reused->start <= k;
        have k < reused->end;
        instantiate(forall (j: int32) {
            allocated == 1 and reused->start <= j and j < reused->end implies
                at(allocating, middle->arena->occupied[j]) == 0
        }, k);
        have 0 <= reused->start;
        have 0 <= k;
        have reused->end <= middle->arena->capacity;
        have k < at(allocating, middle->arena->capacity) by {
            close() using {
                k < reused->end;
                reused->end <= middle->arena->capacity;
                middle->arena->capacity == at(allocating, middle->arena->capacity);
            };
        }
        instantiate(forall (j: int32) {
            0 <= j and j < at(allocating, middle->arena->capacity) implies
                (at(allocating, middle->arena->occupied[j]) == 0 implies 2 <= j and j < 4)
        }, k);
        close();
    }
    have allocated == 1 implies 2 <= reused->start and reused->end <= 4 by {
        intro();
        have reused->start < reused->end;
        instantiate(forall (k: int32) {
            allocated == 1 and reused->start <= k and k < reused->end implies 2 <= k and k < 4
        }, reused->start);
        have reused->start <= 4;
        have reused->end <= 4 by {
            if 4 < reused->end {
                instantiate(forall (k: int32) {
                    allocated == 1 and reused->start <= k and k < reused->end implies
                        2 <= k and k < 4
                }, 4);
                have not (4 < 4) by {
                    close() using {};
                }
                contradiction(4 < 4);
            } else {
                close() using {
                    not (4 < reused->end);
                };
            }
        }
        close();
    }
    step();
    close();
}
