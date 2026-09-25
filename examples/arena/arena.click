import "arena_resources.click";

resource arena_metadata(arena: struct arena*) {
    owns &arena->data;
    owns &arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
    contains allocation(arena->data, arena->capacity * 4);
    contains allocation(arena->occupied, arena->capacity * 4);
    fact 0 <= arena->capacity;
    fact arena->capacity <= 536870911;
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
    owns object(region);
    contains arena_metadata(region->arena);
    owns region->arena->data[region->start..region->end];
    owns region->arena->occupied[region->start..region->end];
}

resource arena_available(region: struct region*) {
    owns region->arena->data[region->start..region->end];
    owns region->arena->occupied[region->start..region->end];
}


resource arena_first_allocation(
    arena: struct arena*,
    region: struct region*
) {
    owns object(region);
    contains arena_metadata(arena);
    owns arena->data[0..region->end];
    owns arena->occupied[0..region->end];
    owns arena->data[region->end..arena->capacity];
    owns arena->occupied[region->end..arena->capacity];
    fact region->arena == arena;
    fact region->start == 0;
}

resource arena_first_alloc_failure(
    arena: struct arena*,
    region: struct region*,
    allocated: int32
) {
    if allocated == 0 {
        contains arena_empty(arena);
        owns object(region);
    }
}

resource arena_first_alloc_success(
    arena: struct arena*,
    region: struct region*,
    allocated: int32
) {
    if allocated == 1 {
        contains arena_first_allocation(arena, region);
    }
}

resource arena_first_alloc_result(
    arena: struct arena*,
    region: struct region*,
    allocated: int32
) {
    contains arena_first_alloc_failure(arena, region, allocated);
    contains arena_first_alloc_success(arena, region, allocated);
    fact allocated == 0 or allocated == 1;
}

verifying "arena_alloc.c";
verifying "arena_region_length.c";
verifying "arena_read.c";
verifying "arena_write.c";
verifying "arena_free.c";

int32 arena_alloc(struct arena* arena, int32 count, struct region* region) {
    requires forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    };
    consumes arena_empty(arena);
    consumes object(region);
    produces arena_first_alloc_result(arena, region, result);

    ensures result == 0 or result == 1;
    ensures result == 0 implies count <= 0 or count > arena->capacity;
    ensures count <= 0 or count > arena->capacity implies result == 0;
    ensures result == 1 implies region->arena == arena;
    ensures result == 1 implies region->start == 0;
    ensures result == 1 implies region->end == count;
    ensures result == 1 implies arena->live_regions == 1;
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
                1
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                1
            ));
            fold(arena_empty(arena));
            fold(arena_first_alloc_failure(arena, region, result));
            fold(arena_first_alloc_success(arena, region, result));
            fold(arena_first_alloc_result(arena, region, result));
            have result == 0 by {
                normalize();
            }
            have result == 0 or result == 1 by {
                left();
            }
            have result == 0 implies
                count <= 0 or count > arena->capacity by {
                intro();
                left();
                assumption();
            }
            have count <= 0 or count > arena->capacity implies
                result == 0 by {
                intro();
                assumption();
            }
            have result == 1 implies region->arena == arena by {
                intro();
                contradiction(result == 1);
            }
            have result == 1 implies region->start == 0 by {
                intro();
                contradiction(result == 1);
            }
            have result == 1 implies region->end == count by {
                intro();
                contradiction(result == 1);
            }
            have result == 1 implies arena->live_regions == 1 by {
                intro();
                contradiction(result == 1);
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
        else {}
    }
    branch {
        then {
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                1
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                1
            ));
            fold(arena_empty(arena));
            fold(arena_first_alloc_failure(arena, region, result));
            fold(arena_first_alloc_success(arena, region, result));
            fold(arena_first_alloc_result(arena, region, result));
            have result == 0 by {
                normalize();
            }
            have result == 0 or result == 1 by {
                left();
            }
            have result == 0 implies
                count <= 0 or count > arena->capacity by {
                intro();
                right();
                assumption();
            }
            have count <= 0 or count > arena->capacity implies
                result == 0 by {
                intro();
                assumption();
            }
            have result == 1 implies region->arena == arena by {
                intro();
                contradiction(result == 1);
            }
            have result == 1 implies region->start == 0 by {
                intro();
                contradiction(result == 1);
            }
            have result == 1 implies region->end == count by {
                intro();
                contradiction(result == 1);
            }
            have result == 1 implies arena->live_regions == 1 by {
                intro();
                contradiction(result == 1);
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
        else {}
    }
    have count > 0 by {
        assumption();
    }
    have count >= 0 by {
        apply(int32_strictly_positive_is_nonnegative(count)) using {
            count > 0;
        }
        assumption();
    }
    have 0 <= count by {
        apply(int32_ge_implies_reversed_le(count, 0)) using {
            count >= 0;
        }
        assumption();
    }
    have count <= arena->capacity by {
        assumption();
    }
    step();
    step();
    loop as find_first_run {
        decreases arena->capacity - i;
        invariant 0 <= i and i <= arena->capacity and
            run_length == i and run_length <= count;
        owns arena->occupied[0..arena->capacity];

        initialize by simp;
        preserve by {
            mark iteration;
            have 0 <= i by {
                simp() using {
                    0 <= i and i <= arena->capacity and
                        run_length == i and run_length <= count;
                }
            }
            have i < arena->capacity by {
                assumption();
            }
            have arena->occupied[i] == 0 by {
                instantiate(forall (k: int32) {
                    0 <= k and k < arena->capacity implies
                        arena->occupied[k] == 0
                }, i) using {
                    0 <= i;
                    i < arena->capacity;
                }
                assumption();
            }
            have run_length + 1 <= count by {
                apply(int32_increment_upper_bound(run_length, count)) using {
                    run_length < count;
                }
                assumption();
            }
            step();
            step();
            step();
            have run_length <= count by {
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
            close_invariants();
        }
    }
    have run_length == i by {
        simp() using {
            0 <= i and i <= arena->capacity and
                run_length == i and run_length <= count;
        }
    }
    have run_length <= count by {
        simp() using {
            0 <= i and i <= arena->capacity and
                run_length == i and run_length <= count;
        }
    }
    have run_length == count by {
        cases(
            not (i < arena->capacity) or not (run_length < count)
        ) {
            have i >= arena->capacity by {
                apply(int32_not_lt_implies_ge(
                    i,
                    arena->capacity
                )) using {
                    not (i < arena->capacity);
                }
                assumption();
            }
            have arena->capacity <= i by {
                apply(int32_ge_implies_reversed_le(
                    i,
                    arena->capacity
                )) using {
                    i >= arena->capacity;
                }
                assumption();
            }
            have count <= i by {
                apply(int32_le_transitive(
                    count,
                    arena->capacity,
                    i
                )) using {
                    count <= arena->capacity;
                    arena->capacity <= i;
                }
                assumption();
            }
            have count <= run_length by {
                rewrite(run_length == i);
                assumption();
            }
            have not (run_length < count) by {
                arithmetic() using {
                    count <= run_length;
                }
            }
            apply(int32_le_and_not_lt_implies_eq(
                run_length,
                count
            )) using {
                run_length <= count;
                not (run_length < count);
            }
            assumption();
        } {
            apply(int32_le_and_not_lt_implies_eq(
                run_length,
                count
            )) using {
                run_length <= count;
                not (run_length < count);
            }
            assumption();
        }
    }
    branch {
        then {
            contradiction(run_length < count);
        }
        else {}
    }
    step();
    step();
    step();
    have start == 0 by {
        simp();
    }
    have end == count by {
        simp();
    }
    have i == start by {
        normalize();
    }
    have start <= i and i <= end by {
        have start <= i by {
            rewrite(i == start);
            normalize();
        }
        have i <= end by {
            rewrite(i == start);
            rewrite(start == 0);
            rewrite(end == count);
            assumption();
        }
        split();
    }
    loop as mark_first_run {
        decreases end - i;
        invariant start <= i and i <= end;
        owns arena->occupied[start..end];

        initialize by simp;
        preserve by {
            mark iteration;
            step();
            step();
            have 0 <= at(iteration, i) by {
                simp();
            }
            have 0 <= end by {
                simp();
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
            close_invariants();
        }
    }
    step();
    step();
    step();
    step();
    step();
    have result == 1 by {
        normalize();
    }
    have result == 0 or result == 1 by {
        right();
    }
    have result == 0 implies
        count <= 0 or count > arena->capacity by {
        intro();
        contradiction(result == 0);
    }
    have count <= 0 or count > arena->capacity implies
        result == 0 by {
        intro();
        cases(count <= 0 or count > arena->capacity) {
            contradiction(count <= 0);
        } {
            contradiction(count > arena->capacity);
        }
    }
    have region->arena == arena by {
        simp();
    }
    have region->start == 0 by {
        simp();
    }
    have region->end == count by {
        simp();
    }
    have arena->live_regions == 1 by {
        simp();
    }
    have result == 1 implies region->arena == arena by {
        intro();
        assumption();
    }
    have result == 1 implies region->start == 0 by {
        intro();
        assumption();
    }
    have result == 1 implies region->end == count by {
        intro();
        assumption();
    }
    have result == 1 implies arena->live_regions == 1 by {
        intro();
        assumption();
    }
    fold(arena_metadata(arena));
    fold(arena_first_allocation(arena, region));
    fold(arena_first_alloc_failure(arena, region, result));
    fold(arena_first_alloc_success(arena, region, result));
    fold(arena_first_alloc_result(arena, region, result));
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 arena_region_length(struct region* region) {
    requires 0 <= region->start;
    requires region->start <= region->end;
    views arena_region(region);

    ensures result == region->end - region->start;
} by {
    open(arena_region(region)) {
        have defined(region->end - region->start) by {
            apply(int32_nonnegative_subtract_within_value_is_defined(
                region->end,
                region->start
            )) using {
                0 <= region->start;
                region->start <= region->end;
            }
        }
        step();
        simp();
    }
}

int32 arena_read(struct region* region, int32 index) {
    requires 0 <= index;
    requires defined(region->start + index) and
        region->start + index < region->end;
    views arena_region(region);

    ensures result == region->arena->data[region->start + index];
} by {
    have defined(region->start + index) by {
        simp() using {
            defined(region->start + index) and
                region->start + index < region->end;
        }
    }
    have region->start + index < region->end by {
        simp() using {
            defined(region->start + index) and
                region->start + index < region->end;
        }
    }
    have 0 <= index by {
        assumption();
    }
    have region->start <= region->start + index by {
        apply(int32_add_nonnegative_right_is_at_least_left(
            region->start,
            index
        )) using {
            0 <= index;
            defined(region->start + index);
        }
    }
    have region->start + index + 1 <= region->end by {
        apply(int32_increment_upper_bound(
            region->start + index,
            region->end
        )) using {
            region->start + index < region->end;
        }
    }
    observe(arena_region(region));
    observe(arena_metadata(region->arena));
    open(arena_region(region)) {
        open(arena_metadata(region->arena)) {
            step();
            step();
            step();
            simp();
        }
    }
}

void arena_write(struct region* region, int32 index, int32 value) {
    requires 0 <= index;
    requires defined(region->start + index) and
        region->start + index < region->end;
    owns arena_region(region);

    ensures region->arena->data[region->start + index] == value;
} by {
    observe(arena_region(region));
    observe(arena_metadata(region->arena));
    open(arena_region(region)) {
        open(arena_metadata(region->arena)) {
            have defined(region->start + index) by {
                simp() using {
                    defined(region->start + index) and
                        region->start + index < region->end;
                }
            }
            have region->start + index < region->end by {
                simp() using {
                    defined(region->start + index) and
                        region->start + index < region->end;
                }
            }
            have 0 <= index by {
                assumption();
            }
            have region->start <= region->start + index by {
                apply(int32_add_nonnegative_right_is_at_least_left(
                    region->start,
                    index
                )) using {
                    0 <= index;
                    defined(region->start + index);
                }
            }
            have region->start + index + 1 <= region->end by {
                apply(int32_increment_upper_bound(
                    region->start + index,
                    region->end
                )) using {
                    region->start + index < region->end;
                }
            }
            execute();
            simp();
        }
    }
}

void arena_free(struct region* region) {
    requires 0 <= region->start;
    requires region->start <= region->end;
    requires region->end <= region->arena->capacity;
    requires 1 <= region->arena->live_regions;
    consumes arena_region(region);
    produces object(region);
    produces arena_metadata(region->arena);
    produces arena_available(region);

    ensures region->arena->live_regions ==
        old(region->arena->live_regions) - 1;
} by {
    unfold(arena_region(region));
    unfold(arena_metadata(region->arena));
    step();
    step();
    step();
    step();
    loop as clear_occupied {
        decreases region->end - i;
        invariant region->start <= i and i <= region->end;
        owns region->arena->occupied[region->start..region->end];
        initialize by {
            have region->start <= i and i <= region->end by {
                have i == region->start by {
                    normalize();
                }
                have region->start <= i by {
                    rewrite(i == region->start);
                    normalize();
                }
                have i <= region->end by {
                    rewrite(i == region->start);
                    assumption();
                }
                split();
            }
        }
        preserve by {
            mark iteration;
            have i < region->end by {
                assumption();
            }
            have i < region->arena->capacity by {
                apply(int32_lt_le_transitive(
                    i,
                    region->end,
                    region->arena->capacity
                )) using {
                    i < region->end;
                    region->end <= region->arena->capacity;
                }
                assumption();
            }
            have region->arena->capacity < 2147483647 by {
                apply(int32_le_lt_transitive(
                    region->arena->capacity,
                    536870911,
                    2147483647
                )) using {
                    region->arena->capacity <= 536870911;
                }
                assumption();
            }
            have i < 2147483647 by {
                apply(int32_lt_transitive(
                    i,
                    region->arena->capacity,
                    2147483647
                )) using {
                    i < region->arena->capacity;
                    region->arena->capacity < 2147483647;
                }
                assumption();
            }
            step();
            step();
            have region->start <= i by {
                simp();
            }
            have i <= region->end by {
                simp();
            }
            have 0 <= at(iteration, i) by {
                simp();
            }
            have 0 <= region->end by {
                simp() using {
                    0 <= region->start;
                    region->start <= region->end;
                }
            }
            have 0 <= 0 - at(iteration, i) + region->end - 1 by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    0 <= region->end;
                    at(iteration, i) < at(iteration, region->end);
                }
            }
            have 0 - at(iteration, i) + region->end - 1
                < 0 - at(iteration, i) + region->end by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    0 <= region->end;
                    at(iteration, i) < at(iteration, region->end);
                }
            }
            close_invariants();
        }
    }
    step();
    step();
    fold(arena_available(region));
    fold(arena_metadata(region->arena));
    simp();
}
