spec enum ArenaOneTag { One }
spec enum ArenaTwoTag { Two }

spec enum ArenaSecondAllocOutcome {
    Failure(ArenaOneTag),
    Success(ArenaTwoTag),
}

resource arena_after_first_two(arena: struct arena*) {
    field tag: ArenaOneTag;
    match tag {
        ArenaOneTag::One => {
            owns arena->data;
            owns arena->occupied;
            owns arena->capacity;
            owns arena->live_regions;
            owns arena->occupied[0..arena->capacity];
            owns arena->data[2..arena->capacity];
            fact 2 <= arena->capacity;
            fact arena->capacity <= 536870911;
            fact arena->live_regions == 1;
            fact separate(
                memory(object(arena)),
                memory(arena->data[0..arena->capacity])
            );
            fact separate(
                memory(object(arena)),
                memory(arena->occupied[0..arena->capacity])
            );
        },
    }
}

resource arena_after_second_two(arena: struct arena*) {
    field tag: ArenaTwoTag;
    match tag {
        ArenaTwoTag::Two => {
            owns arena->data;
            owns arena->occupied;
            owns arena->capacity;
            owns arena->live_regions;
            owns arena->occupied[0..arena->capacity];
            owns arena->data[4..arena->capacity];
            fact 4 <= arena->capacity;
            fact arena->capacity <= 536870911;
            fact arena->live_regions == 2;
            fact separate(
                memory(object(arena)),
                memory(arena->data[0..arena->capacity])
            );
            fact separate(
                memory(object(arena)),
                memory(arena->occupied[0..arena->capacity])
            );
        },
    }
}

resource arena_second_region(
    arena: struct arena*,
    region: struct region*
) {
    field tag: ArenaTwoTag;
    match tag {
        ArenaTwoTag::Two => {
            owns object(region);
            owns arena->data[2..4];
            fact region->arena == arena;
            fact region->start == 2;
            fact region->end == 4;
        },
    }
}

resource arena_second_alloc_result(
    arena: struct arena*,
    region: struct region*
) {
    field model: ArenaSecondAllocOutcome;
    match model {
        ArenaSecondAllocOutcome::Failure(tag) => {
            owns state: arena_after_first_two(arena);
            owns object(region);
            fact state.tag == tag;
        },
        ArenaSecondAllocOutcome::Success(tag) => {
            owns state: arena_after_second_two(arena);
            owns allocated: arena_second_region(arena, region);
            fact state.tag == tag;
            fact allocated.tag == tag;
        },
    }
}

verifying "arena_alloc.c";

int32 arena_alloc(struct arena* arena, int32 count, struct region* region) {
    owns arena->data[0..2];
    consumes before: arena_after_first_two(arena);
    requires before.tag == ArenaOneTag::One;
    requires count == 2;
    requires forall (k: int32) {
        0 <= k and k < arena->capacity and k < 2 implies
            arena->occupied[k] == 1
    };
    requires forall (k: int32) {
        2 <= k and k < arena->capacity implies arena->occupied[k] == 0
    };
    consumes object(region);
    produces outcome: arena_second_alloc_result(arena, region);

    ensures result == 0 or result == 1;
    ensures result == 0 implies outcome.model ==
        ArenaSecondAllocOutcome::Failure(ArenaOneTag::One);
    ensures result == 1 implies outcome.model ==
        ArenaSecondAllocOutcome::Success(ArenaTwoTag::Two);
    ensures result == 1 implies region->arena == arena;
    ensures result == 1 implies region->start == 2;
    ensures result == 1 implies region->end == 4;
    ensures result == 1 implies arena->live_regions == 2;
} by {
    match before.tag {
        ArenaOneTag::One => {
            unfold(before);
            step();
            step();
            step();
            step();
            branch {
                then { contradiction(count <= 0); }
                else {}
            }
            branch {
                then { contradiction(count > arena->capacity); }
                else {}
            }
            step();
            step();
            loop as find_adjacent_run {
                invariant 0 <= i and i <= arena->capacity;
                invariant 0 <= run_length and run_length <= 2;
                invariant (i <= 2 and run_length == 0) or
                    (2 <= i and 2 + run_length == i);
                owns arena->occupied[0..arena->capacity];

                initialize by simp;
                preserve by {
                    if i < 2 {
                        have i + 1 <= arena->capacity by {
                            apply(int32_increment_upper_bound(
                                i,
                                arena->capacity
                            )) using {
                                i < arena->capacity;
                            }
                            assumption();
                        }
                        have arena->occupied[i] == 1 by {
                            instantiate(forall (k: int32) {
                                0 <= k and k < arena->capacity and k < 2 implies
                                    arena->occupied[k] == 1
                            }, i) using {
                                0 <= i;
                                i < arena->capacity;
                                i < 2;
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
                        have 0 <= run_length and run_length <= 2 by {
                            simp();
                        }
                        have i <= 2 and run_length == 0 by {
                            simp();
                        }
                        have (i <= 2 and run_length == 0) or
                            (2 <= i and 2 + run_length == i) by {
                            left();
                        }
                        close_invariants();
                    } else {
                        have 2 <= i by {
                            arithmetic() using { not (i < 2); }
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
                        have 2 + run_length == i by {
                            cases(
                                (i <= 2 and run_length == 0) or
                                    (2 <= i and 2 + run_length == i)
                            ) {
                                extract(i <= 2);
                                extract(run_length == 0);
                                have i == 2 by {
                                    apply(int32_le_and_not_lt_implies_eq(
                                        i,
                                        2
                                    )) using {
                                        i <= 2;
                                        not (i < 2);
                                    }
                                    assumption();
                                }
                                rewrite(run_length == 0);
                                rewrite(i == 2);
                                normalize() using {
                                    i <= 2;
                                };
                            } {
                                extract(2 + run_length == i);
                                assumption();
                            }
                        }
                        have arena->occupied[i] == 0 by {
                            instantiate(forall (k: int32) {
                                2 <= k and k < arena->capacity implies
                                    arena->occupied[k] == 0
                            }, i) using {
                                2 <= i;
                                i < arena->capacity;
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
                        have 0 <= run_length and run_length <= 2 by {
                            simp();
                        }
                        have 2 <= i and 2 + run_length == i by {
                            simp();
                        }
                        have (i <= 2 and run_length == 0) or
                            (2 <= i and 2 + run_length == i) by {
                            right();
                        }
                        close_invariants();
                    }
                }
            }
            branch {
                then {
                    step();
                    let restored = fold(arena_after_first_two(arena), {
                        tag: ArenaOneTag::One
                    });
                    let outcome = fold(arena_second_alloc_result(arena, region), {
                        model: ArenaSecondAllocOutcome::Failure(ArenaOneTag::One)
                    }, { state: restored });
                    simp();
                }
                else {}
            }
            have run_length <= 2 by {
                simp() using {
                    0 <= run_length and run_length <= 2;
                }
            }
            have not (run_length < 2) by {
                simp();
            }
            have run_length == 2 by {
                apply(int32_le_and_not_lt_implies_eq(
                    run_length,
                    2
                )) using {
                    run_length <= 2;
                    not (run_length < 2);
                }
                assumption();
            }
            have 2 + run_length == i by {
                cases(
                    (i <= 2 and run_length == 0) or
                        (2 <= i and 2 + run_length == i)
                ) {
                    extract(run_length == 0);
                    have not (run_length == 0) by {
                        rewrite(run_length == 2);
                        normalize();
                    }
                    contradiction(run_length == 0);
                } {
                    extract(2 + run_length == i);
                    assumption();
                }
            }
            have i == 4 by {
                have i == 2 + run_length by {
                    simp() using {
                        2 + run_length == i;
                    }
                }
                have 2 + run_length == 4 by {
                    rewrite(run_length == 2);
                    normalize();
                }
                rewrite(i == 2 + run_length);
                assumption();
            }
            step();
            have start == 2 by {
                simp() using {
                    i == 4;
                    count == 2;
                }
            }
            step();
            have end == 4 by {
                simp() using {
                    i == 4;
                }
            }
            step();
            have i == 2 by {
                simp() using {
                    start == 2;
                }
            }
            loop as mark_adjacent_run {
                invariant 2 <= i and i <= 4;
                owns arena->occupied[0..arena->capacity];

                initialize by simp;
                preserve by {
                    step();
                    step();
                    simp();
                }
            }
            step();
            have region->arena == arena by {
                normalize() using { }
            }
            step();
            have region->start == 2 by {
                simp() using {
                    start == 2;
                }
            }
            step();
            have region->end == 4 by {
                simp() using {
                    end == 4;
                }
            }
            step();
            have arena->live_regions == 2 by {
                simp();
            }
            step();
            have result == 1 by {
                normalize();
            }
            let remaining = fold(arena_after_second_two(arena), {
                tag: ArenaTwoTag::Two
            });
            let allocated = fold(arena_second_region(arena, region), {
                tag: ArenaTwoTag::Two
            });
            let outcome = fold(arena_second_alloc_result(arena, region), {
                model: ArenaSecondAllocOutcome::Success(ArenaTwoTag::Two)
            }, { state: remaining, allocated: allocated });
            have result == 0 or result == 1 by {
                right();
            }
            have result == 0 implies outcome.model ==
                ArenaSecondAllocOutcome::Failure(ArenaOneTag::One) by {
                intro();
                contradiction(result == 0);
            }
            have outcome.model ==
                ArenaSecondAllocOutcome::Success(ArenaTwoTag::Two) by {
                assumption();
            }
            have result == 1 implies outcome.model ==
                ArenaSecondAllocOutcome::Success(ArenaTwoTag::Two) by {
                intro();
                assumption();
            }
            have region->arena == arena by {
                assumption();
            }
            have region->start == 2 by {
                assumption();
            }
            have region->end == 4 by {
                assumption();
            }
            have arena->live_regions == 2 by {
                assumption();
            }
            have result == 1 implies region->arena == arena by {
                intro();
                assumption();
            }
            have result == 1 implies region->start == 2 by {
                intro();
                assumption();
            }
            have result == 1 implies region->end == 4 by {
                intro();
                assumption();
            }
            have result == 1 implies arena->live_regions == 2 by {
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
            assumption();
        },
    }
}
