verifying "nested.rs";
uint64 array_len() { ensures result == 8u64; } by { execute(); simp(); }
uint8 array_mut() { ensures result == 9; } by { execute(); simp(); }

theorem chunk_offset_shift(x: int32, y: int32) {
    requires 0 <= x;
    requires x <= 4;
    requires 0 <= y;
    requires y <= 4;
    ensures 8 - x - y == (8 - x - (y + 2)) + 2 by {
        arithmetic() using { 0 <= x; x <= 4; 0 <= y; y <= 4; }
    }
}

uint64 nested(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 8u64;
    views bytes[0..8];
    ensures result == 0u64;
    ensures forall (k: int32) { 0 <= k and k < 8 implies bytes[k] == old(bytes[k]) };
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have viewable(bytes[0..8]) by {
        transport(at(function.entry, viewable(bytes[0..8])), viewable(bytes[0..8])) using {
            at(function.entry, viewable(bytes[0..8]));
        }
    }
    loop {
        decreases __rust_mir_8_remaining;
        views bytes[0..8];
        invariant viewable(bytes[0..8]);
        invariant __rust_mir_8_size == 4u64;
        invariant 0 <= __rust_mir_8_remaining and __rust_mir_8_remaining <= 8;
        invariant (__rust_mir_8_remaining % 4) == 0;
        invariant __rust_mir_8_cursor == (bytes + (8 - __rust_mir_8_remaining));
        invariant __rust_mir_14_live == 0;
        invariant __rust_mir_15_live == 0;
        invariant __rust_mir_17_live == 0;
        initialize by {
            have viewable(bytes[0..8]) by {
                assumption();
            }
            have __rust_mir_8_size == 4u64 by {
                normalize();
            }
            have 0 <= __rust_mir_8_remaining and __rust_mir_8_remaining <= 8 by {
                both {
                    rewrite(at(function.entry, bytes_len) == at(function.entry, 8u64));
                    normalize();
                } and {
                    rewrite(at(function.entry, bytes_len) == at(function.entry, 8u64));
                    normalize();
                }
            }
            have (__rust_mir_8_remaining % 4) == 0 by {
                rewrite(at(function.entry, bytes_len) == at(function.entry, 8u64));
                normalize();
            }
            have __rust_mir_8_cursor == (bytes + (8 - __rust_mir_8_remaining)) by {
                rewrite(at(function.entry, bytes_len) == at(function.entry, 8u64));
                intro();
                intro();
                intro();
                normalize();
            }
            have __rust_mir_14_live == 0 by {
                intro();
                intro();
                intro();
                intro();
                normalize();
            }
            have __rust_mir_15_live == 0 by {
                intro();
                intro();
                intro();
                intro();
                intro();
                normalize();
            }
            have __rust_mir_17_live == 0 by {
                intro();
                intro();
                intro();
                intro();
                intro();
                intro();
                normalize();
            }
        }
        preserve by {
            have 4 <= __rust_mir_8_remaining by {
                assumption();
            }
            have 0 <= (8 - __rust_mir_8_remaining) by {
                arithmetic_certificate signed_int32 {
                    premise 0: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                    premise 1: __rust_mir_8_remaining <= 8 => __rust_mir_8_remaining <= 8;
                    interval_atom (8) (8) (8);
                    interval_from_affine 0 (__rust_mir_8_remaining) (0) (2147483647);
                    interval_from_affine 1 (__rust_mir_8_remaining) (-2147483648) (8);
                    interval_intersect 3, 4 (0) (8);
                    interval_subtract 2, 5 2 (0) (8);
                    affine_conclusion 1 6 => 0 <= (8 - __rust_mir_8_remaining);
                    conclusion 7;
                }
            }
            have (8 - __rust_mir_8_remaining) <= 8 by {
                arithmetic_certificate signed_int32 {
                    premise 0: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                    premise 1: __rust_mir_8_remaining <= 8 => __rust_mir_8_remaining <= 8;
                    interval_atom (8) (8) (8);
                    interval_from_affine 0 (__rust_mir_8_remaining) (0) (2147483647);
                    interval_from_affine 1 (__rust_mir_8_remaining) (-2147483648) (8);
                    interval_intersect 3, 4 (0) (8);
                    interval_subtract 2, 5 2 (0) (8);
                    affine_conclusion 0 6 => (8 - __rust_mir_8_remaining) <= 8;
                    conclusion 7;
                }
            }
            mark outer;
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            have __rust_mir_8_remaining == (at(outer, __rust_mir_8_remaining) - 4) by {
                normalize();
            }
            have 0 <= __rust_mir_8_remaining by {
                arithmetic_certificate signed_int32 {
                    premise 0: at(outer, 4 <= __rust_mir_8_remaining) => at(outer, 4 <= __rust_mir_8_remaining);
                    interval_from_affine 0 (at(outer, __rust_mir_8_remaining)) (4) (2147483647);
                    interval_atom (4) (4) (4);
                    interval_subtract 1, 2 1 (0) (2147483643);
                    affine_conclusion 0 3 => 0 <= __rust_mir_8_remaining;
                    conclusion 4;
                }
            }
            have __rust_mir_8_remaining <= 4 by {
                arithmetic_certificate signed_int32 {
                    premise 0: at(outer, __rust_mir_8_remaining <= 8) => at(outer, __rust_mir_8_remaining <= 8);
                    premise 1: at(outer, 4 <= __rust_mir_8_remaining) => at(outer, 4 <= __rust_mir_8_remaining);
                    interval_from_affine 1 (at(outer, __rust_mir_8_remaining)) (4) (2147483647);
                    interval_from_affine 0 (at(outer, __rust_mir_8_remaining)) (-2147483648) (8);
                    interval_intersect 2, 3 (4) (8);
                    interval_atom (4) (4) (4);
                    interval_subtract 4, 5 4 (0) (4);
                    affine_conclusion 0 6 => __rust_mir_8_remaining <= 4;
                    conclusion 7;
                }
            }
            have chunk == at(outer, __rust_mir_8_cursor) by {
                normalize();
            }
            have ((8 - __rust_mir_8_remaining) - 4) == (8 - at(outer, __rust_mir_8_remaining)) by {
                arithmetic_certificate signed_int32 {
                    premise 0: __rust_mir_8_remaining == (at(outer, __rust_mir_8_remaining) - 4) => __rust_mir_8_remaining == (at(outer, __rust_mir_8_remaining) - 4);
                    premise 1: at(outer, 4 <= __rust_mir_8_remaining) => at(outer, 4 <= __rust_mir_8_remaining);
                    premise 2: at(outer, __rust_mir_8_remaining <= 8) => at(outer, __rust_mir_8_remaining <= 8);
                    interval_atom (8) (8) (8);
                    interval_from_affine 1 (at(outer, __rust_mir_8_remaining)) (4) (2147483647);
                    interval_from_affine 2 (at(outer, __rust_mir_8_remaining)) (-2147483648) (8);
                    interval_intersect 4, 5 (4) (8);
                    interval_atom (4) (4) (4);
                    interval_subtract 6, 7 6 (0) (4);
                    interval_subtract 3, 8 3 (4) (8);
                    interval_subtract 9, 7 9 (0) (4);
                    interval_subtract 3, 6 3 (0) (4);
                    affine_conclusion_pair 0 10 11 => ((8 - __rust_mir_8_remaining) - 4) == (8 - at(outer, __rust_mir_8_remaining));
                    conclusion 12;
                }
            }
            have chunk == (bytes + ((8 - __rust_mir_8_remaining) - 4)) by {
                rewrite(((8 - __rust_mir_8_remaining) - 4) == (8 - at(outer, __rust_mir_8_remaining)));
                assumption();
            }
            have __rust_mir_17_remaining == 4 by {
                normalize();
            }
            have __rust_mir_17_cursor == (bytes + ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) by {
                rewrite(__rust_mir_17_remaining == 4);
                assumption();
            }
            have 0 <= ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) by {
                arithmetic_certificate signed_int32 {
                    premise 0: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                    premise 1: __rust_mir_8_remaining <= 4 => __rust_mir_8_remaining <= 4;
                    interval_atom (0) (0) (0);
                    interval_atom (8) (8) (8);
                    interval_from_affine_direct 0 (__rust_mir_8_remaining) (0) (2147483647);
                    interval_from_affine_direct 1 (__rust_mir_8_remaining) (-2147483648) (4);
                    interval_intersect 4, 5 (0) (4);
                    interval_subtract 3, 6 3 (4) (8);
                    interval_atom (4) (4) (4);
                    interval_subtract 7, 8 7 (0) (4);
                    interval_compare 2, 9 le => 0 <= ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining);
                    conclusion 10;
                }
            }
            have ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) <= 8 by {
                arithmetic_certificate signed_int32 {
                    premise 0: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                    premise 1: __rust_mir_8_remaining <= 4 => __rust_mir_8_remaining <= 4;
                    interval_atom (8) (8) (8);
                    interval_from_affine_direct 0 (__rust_mir_8_remaining) (0) (2147483647);
                    interval_from_affine_direct 1 (__rust_mir_8_remaining) (-2147483648) (4);
                    interval_intersect 3, 4 (0) (4);
                    interval_subtract 2, 5 2 (4) (8);
                    interval_atom (4) (4) (4);
                    interval_subtract 6, 7 6 (0) (4);
                    interval_compare 8, 2 le => ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) <= 8;
                    conclusion 9;
                }
            }
            have viewable(bytes[0..8]) by {
                transport(at(outer, viewable(bytes[0..8])), viewable(bytes[0..8])) using {
                    at(outer, viewable(bytes[0..8]));
                }
            }
            have 4 <= (8 - __rust_mir_8_remaining) by {
                arithmetic_certificate signed_int32 {
                    premise 0: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                    premise 1: __rust_mir_8_remaining <= 4 => __rust_mir_8_remaining <= 4;
                    interval_atom (4) (4) (4);
                    interval_atom (8) (8) (8);
                    interval_from_affine_direct 0 (__rust_mir_8_remaining) (0) (2147483647);
                    interval_from_affine_direct 1 (__rust_mir_8_remaining) (-2147483648) (4);
                    interval_intersect 4, 5 (0) (4);
                    interval_subtract 3, 6 3 (4) (8);
                    interval_compare 2, 7 le => 4 <= (8 - __rust_mir_8_remaining);
                    conclusion 8;
                }
            }
            have (8 - __rust_mir_8_remaining) <= 8 by {
                arithmetic_certificate signed_int32 {
                    premise 0: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                    premise 1: __rust_mir_8_remaining <= 4 => __rust_mir_8_remaining <= 4;
                    interval_atom (8) (8) (8);
                    interval_from_affine_direct 0 (__rust_mir_8_remaining) (0) (2147483647);
                    interval_from_affine_direct 1 (__rust_mir_8_remaining) (-2147483648) (4);
                    interval_intersect 3, 4 (0) (4);
                    interval_subtract 2, 5 2 (4) (8);
                    interval_compare 6, 2 le => (8 - __rust_mir_8_remaining) <= 8;
                    conclusion 7;
                }
            }
            have ((at(outer, __rust_mir_8_remaining) - 4) % 4) == at(outer, (__rust_mir_8_remaining % 4)) by {
                normalize() using {
                    at(outer, 4 <= __rust_mir_8_remaining);
                }
            }
            have (__rust_mir_8_remaining % 4) == 0 by {
                rewrite(__rust_mir_8_remaining == (at(outer, __rust_mir_8_remaining) - 4));
                rewrite(((at(outer, __rust_mir_8_remaining) - 4) % 4) == at(outer, (__rust_mir_8_remaining % 4)));
                assumption();
            }
            have (8 - __rust_mir_8_remaining) == (at(outer, (8 - __rust_mir_8_remaining)) + 4) by {
                arithmetic_certificate signed_int32 {
                    premise 0: __rust_mir_8_remaining == (at(outer, __rust_mir_8_remaining) - 4) => __rust_mir_8_remaining == (at(outer, __rust_mir_8_remaining) - 4);
                    premise 1: at(outer, 4 <= __rust_mir_8_remaining) => at(outer, 4 <= __rust_mir_8_remaining);
                    premise 2: at(outer, __rust_mir_8_remaining <= 8) => at(outer, __rust_mir_8_remaining <= 8);
                    interval_atom (8) (8) (8);
                    interval_from_affine 1 (at(outer, __rust_mir_8_remaining)) (4) (2147483647);
                    interval_from_affine 2 (at(outer, __rust_mir_8_remaining)) (-2147483648) (8);
                    interval_intersect 4, 5 (4) (8);
                    interval_atom (4) (4) (4);
                    interval_subtract 6, 7 6 (0) (4);
                    interval_subtract 3, 8 3 (4) (8);
                    interval_subtract 3, 6 3 (0) (4);
                    interval_add_bounded 10, 7 (4) (8);
                    affine_conclusion_pair 0 9 11 => (8 - __rust_mir_8_remaining) == (at(outer, (8 - __rust_mir_8_remaining)) + 4);
                    conclusion 12;
                }
            }
            have (at(outer, __rust_mir_8_cursor) + 4) == (bytes + (at(outer, (8 - __rust_mir_8_remaining)) + 4)) by {
                arithmetic_certificate special {
                    premise 0: at(outer, __rust_mir_8_cursor == (bytes + (8 - __rust_mir_8_remaining))) => at(outer, __rust_mir_8_cursor == (bytes + (8 - __rust_mir_8_remaining)));
                    premise 1: at(outer, 0 <= (8 - __rust_mir_8_remaining)) => at(outer, 0 <= (8 - __rust_mir_8_remaining));
                    premise 2: at(outer, (8 - __rust_mir_8_remaining) <= 8) => at(outer, (8 - __rust_mir_8_remaining) <= 8);
                    pointer_translation relation 0 bounds [1, 2] => (at(outer, __rust_mir_8_cursor) + 4) == (bytes + (at(outer, (8 - __rust_mir_8_remaining)) + 4));
                    conclusion 0;
                }
            }
            have __rust_mir_8_cursor == (bytes + (8 - __rust_mir_8_remaining)) by {
                rewrite((8 - __rust_mir_8_remaining) == (at(outer, (8 - __rust_mir_8_remaining)) + 4));
                assumption();
            }
            loop {
                decreases __rust_mir_17_remaining;
                views bytes[0..8];
                invariant viewable(bytes[0..8]);
                invariant 0 <= __rust_mir_8_remaining and __rust_mir_8_remaining <= 4;
                invariant (__rust_mir_8_remaining % 4) == 0;
                invariant __rust_mir_8_cursor == (bytes + (8 - __rust_mir_8_remaining));
                invariant __rust_mir_17_size == 2u64;
                invariant 0 <= __rust_mir_17_remaining and __rust_mir_17_remaining <= 4;
                invariant (__rust_mir_17_remaining % 2) == 0;
                invariant __rust_mir_17_cursor == (bytes + ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining));
                invariant 0 <= ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) and ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) <= 8;
                invariant 4 <= (8 - __rust_mir_8_remaining) and (8 - __rust_mir_8_remaining) <= 8;
                initialize by {
                    have viewable(bytes[0..8]) by {
                        extract(at(statement(158).entry, 0) <= at(statement(158).entry, __rust_mir_8_remaining));
                    }
                    have 0 <= __rust_mir_8_remaining and __rust_mir_8_remaining <= 4 by {
                        both {
                            assumption();
                        } and {
                            assumption();
                        }
                    }
                    have (__rust_mir_8_remaining % 4) == 0 by {
                        normalize() using {
                            at(statement(158).entry, ((int32)((uint32)__rust_mir_8_size))) <= at(statement(158).entry, __rust_mir_8_remaining);
                        }
                    }
                    have __rust_mir_8_cursor == (bytes + (8 - __rust_mir_8_remaining)) by {
                        intro();
                        assumption();
                    }
                    have __rust_mir_17_size == 2u64 by {
                        intro();
                        intro();
                        normalize();
                    }
                    have 0 <= __rust_mir_17_remaining and __rust_mir_17_remaining <= 4 by {
                        intro();
                        intro();
                        intro();
                        split();
                    }
                    have (__rust_mir_17_remaining % 2) == 0 by {
                        intro();
                        intro();
                        intro();
                        intro();
                        normalize();
                    }
                    have __rust_mir_17_cursor == (bytes + ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) by {
                        intro();
                        intro();
                        intro();
                        intro();
                        intro();
                        intro();
                        assumption();
                    }
                    have 0 <= ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) and ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) <= 8 by {
                        intro();
                        intro();
                        intro();
                        intro();
                        intro();
                        intro();
                        intro();
                        split();
                    }
                    have 4 <= (8 - __rust_mir_8_remaining) and (8 - __rust_mir_8_remaining) <= 8 by {
                        intro();
                        intro();
                        intro();
                        intro();
                        intro();
                        intro();
                        intro();
                        intro();
                        split();
                    }
                }
                preserve by {
                    have 2 <= __rust_mir_17_remaining by {
                        assumption();
                    }
                    have ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) <= 6 by {
                        arithmetic_certificate signed_int32 {
                            premise 0: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                            premise 1: __rust_mir_8_remaining <= 4 => __rust_mir_8_remaining <= 4;
                            premise 2: 2 <= __rust_mir_17_remaining => 2 <= __rust_mir_17_remaining;
                            premise 3: __rust_mir_17_remaining <= 4 => __rust_mir_17_remaining <= 4;
                            interval_atom (8) (8) (8);
                            interval_from_affine_direct 0 (__rust_mir_8_remaining) (0) (2147483647);
                            interval_from_affine_direct 1 (__rust_mir_8_remaining) (-2147483648) (4);
                            interval_intersect 5, 6 (0) (4);
                            interval_subtract 4, 7 4 (4) (8);
                            interval_from_affine 2 (__rust_mir_17_remaining) (2) (2147483647);
                            interval_from_affine 3 (__rust_mir_17_remaining) (-2147483648) (4);
                            interval_intersect 9, 10 (2) (4);
                            interval_subtract 8, 11 8 (0) (6);
                            interval_atom (6) (6) (6);
                            interval_compare 12, 13 le => ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) <= 6;
                            conclusion 14;
                        }
                    }
                    mark inner;
                    have 0 <= ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) by {
                        arithmetic_certificate signed_int32 {
                            premise 0: __rust_mir_8_remaining <= 4 => __rust_mir_8_remaining <= 4;
                            premise 1: __rust_mir_17_remaining <= 4 => __rust_mir_17_remaining <= 4;
                            premise 2: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                            premise 3: 0 <= __rust_mir_17_remaining => 0 <= __rust_mir_17_remaining;
                            interval_atom (0) (0) (0);
                            interval_atom (8) (8) (8);
                            interval_from_affine_direct 2 (__rust_mir_8_remaining) (0) (2147483647);
                            interval_from_affine_direct 0 (__rust_mir_8_remaining) (-2147483648) (4);
                            interval_intersect 6, 7 (0) (4);
                            interval_subtract 5, 8 5 (4) (8);
                            interval_from_affine 3 (__rust_mir_17_remaining) (0) (2147483647);
                            interval_from_affine 1 (__rust_mir_17_remaining) (-2147483648) (4);
                            interval_intersect 10, 11 (0) (4);
                            interval_subtract 9, 12 9 (0) (8);
                            interval_compare 4, 13 le => 0 <= ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining);
                            conclusion 14;
                        }
                    }
                    have (((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) + 2) <= 8 by {
                        arithmetic_certificate signed_int32 {
                            premise 0: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                            premise 1: 2 <= __rust_mir_17_remaining => 2 <= __rust_mir_17_remaining;
                            premise 2: __rust_mir_8_remaining <= 4 => __rust_mir_8_remaining <= 4;
                            premise 3: __rust_mir_17_remaining <= 4 => __rust_mir_17_remaining <= 4;
                            interval_atom (8) (8) (8);
                            interval_from_affine_direct 0 (__rust_mir_8_remaining) (0) (2147483647);
                            interval_from_affine_direct 2 (__rust_mir_8_remaining) (-2147483648) (4);
                            interval_intersect 5, 6 (0) (4);
                            interval_subtract 4, 7 4 (4) (8);
                            interval_from_affine 1 (__rust_mir_17_remaining) (2) (2147483647);
                            interval_from_affine 3 (__rust_mir_17_remaining) (-2147483648) (4);
                            interval_intersect 9, 10 (2) (4);
                            interval_subtract 8, 11 8 (0) (6);
                            interval_atom (2) (2) (2);
                            interval_add_bounded 12, 13 (2) (8);
                            interval_compare 14, 4 le => (((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) + 2) <= 8;
                            conclusion 15;
                        }
                    }
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    have viewable(bytes[0..8]) by {
                        transport(at(inner, viewable(bytes[0..8])), viewable(bytes[0..8])) using {
                            at(inner, viewable(bytes[0..8]));
                        }
                    }
                    have __rust_mir_17_remaining == (at(inner, __rust_mir_17_remaining) - 2) by {
                        normalize();
                    }
                    have ((at(inner, __rust_mir_17_remaining) - 2) % 2) == at(inner, (__rust_mir_17_remaining % 2)) by {
                        normalize() using {
                            at(inner, 2 <= __rust_mir_17_remaining);
                        }
                    }
                    have (__rust_mir_17_remaining % 2) == 0 by {
                        rewrite(__rust_mir_17_remaining == (at(inner, __rust_mir_17_remaining) - 2));
                        rewrite(((at(inner, __rust_mir_17_remaining) - 2) % 2) == at(inner, (__rust_mir_17_remaining % 2)));
                        assumption();
                    }
                    have 0 <= __rust_mir_17_remaining by {
                        arithmetic_certificate signed_int32 {
                            premise 0: at(inner, 2 <= __rust_mir_17_remaining) => at(inner, 2 <= __rust_mir_17_remaining);
                            interval_from_affine 0 (at(inner, __rust_mir_17_remaining)) (2) (2147483647);
                            interval_atom (2) (2) (2);
                            interval_subtract 1, 2 1 (0) (2147483645);
                            affine_conclusion 0 3 => 0 <= __rust_mir_17_remaining;
                            conclusion 4;
                        }
                    }
                    have __rust_mir_17_remaining <= 4 by {
                        arithmetic_certificate signed_int32 {
                            premise 0: at(inner, __rust_mir_17_remaining <= 4) => at(inner, __rust_mir_17_remaining <= 4);
                            premise 1: at(inner, 2 <= __rust_mir_17_remaining) => at(inner, 2 <= __rust_mir_17_remaining);
                            interval_from_affine 1 (at(inner, __rust_mir_17_remaining)) (2) (2147483647);
                            interval_from_affine 0 (at(inner, __rust_mir_17_remaining)) (-2147483648) (4);
                            interval_intersect 2, 3 (2) (4);
                            interval_atom (2) (2) (2);
                            interval_subtract 4, 5 4 (0) (2);
                            trivial => -2 <= 0;
                            add 0, 7 => (at(inner, __rust_mir_17_remaining) + -2) <= (at(inner, 4) + 0);
                            affine_conclusion 8 6 => __rust_mir_17_remaining <= 4;
                            conclusion 9;
                        }
                    }
                    have __rust_mir_8_remaining == at(inner, __rust_mir_8_remaining) by {
                        normalize();
                    }
                    have 4 <= (8 - __rust_mir_8_remaining) and (8 - __rust_mir_8_remaining) <= 8 by {
                        assumption();
                    }
                    have at(inner, __rust_mir_8_remaining) == __rust_mir_8_remaining by {
                        normalize();
                    }
                    have at(inner, __rust_mir_17_remaining) == (__rust_mir_17_remaining + 2) by {
                        arithmetic_certificate signed_int32 {
                            trivial => 0 == 0;
                            conclusion 0;
                        }
                    }
                    have at(inner, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) == ((8 - at(inner, __rust_mir_8_remaining)) - at(inner, __rust_mir_17_remaining)) by {
                        normalize();
                    }
                    have ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) == (at(inner, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) + 2) by {
                        rewrite(at(inner, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) == ((8 - at(inner, __rust_mir_8_remaining)) - at(inner, __rust_mir_17_remaining)));
                        rewrite(at(inner, __rust_mir_8_remaining) == __rust_mir_8_remaining);
                        rewrite(at(inner, __rust_mir_17_remaining) == (__rust_mir_17_remaining + 2));
                        apply(chunk_offset_shift(__rust_mir_8_remaining, __rust_mir_17_remaining)) using {
                            0 <= __rust_mir_8_remaining;
                            __rust_mir_8_remaining <= 4;
                            0 <= __rust_mir_17_remaining;
                            __rust_mir_17_remaining <= 4;
                        }
                    }
                    have (at(inner, __rust_mir_17_cursor) + 2) == (bytes + (at(inner, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) + 2)) by {
                        arithmetic_certificate special {
                            premise 0: at(inner, __rust_mir_17_cursor == (bytes + ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining))) => at(inner, __rust_mir_17_cursor == (bytes + ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)));
                            premise 1: at(inner, 0 <= ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) => at(inner, 0 <= ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining));
                            premise 2: at(inner, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) <= 6) => at(inner, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) <= 6);
                            pointer_translation relation 0 bounds [1, 2] => (at(inner, __rust_mir_17_cursor) + 2) == (bytes + (at(inner, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) + 2));
                            conclusion 0;
                        }
                    }
                    have __rust_mir_17_cursor == (bytes + ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) by {
                        rewrite(((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) == (at(inner, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) + 2));
                        assumption();
                    }
                    close_invariants by {
                        extract(at(statement(226).entry, 0) <= at(statement(226).entry, __rust_mir_17_remaining));
                        extract(at(statement(226).entry, __rust_mir_17_remaining) <= at(statement(226).entry, 4));
                        extract(at(statement(226).entry, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) <= at(statement(226).entry, 8));
                        both {
                            intro();
                            assumption();
                        } and {
                            both {
                                intro();
                                intro();
                                arithmetic_certificate signed_int32 {
                                    trivial => 0 == 0;
                                    conclusion 0;
                                }
                            } and {
                                both {
                                    intro();
                                    intro();
                                    intro();
                                    both {
                                        arithmetic_certificate signed_int32 {
                                            premise 0: 0 <= __rust_mir_17_remaining => 0 <= __rust_mir_17_remaining;
                                            conclusion 0;
                                        }
                                    } and {
                                        arithmetic_certificate signed_int32 {
                                            premise 0: __rust_mir_17_remaining <= 4 => __rust_mir_17_remaining <= 4;
                                            conclusion 0;
                                        }
                                    }
                                } and {
                                    both {
                                        intro();
                                        intro();
                                        intro();
                                        intro();
                                        arithmetic_certificate signed_int32 {
                                            premise 0: (__rust_mir_17_remaining % 2) == 0 => (__rust_mir_17_remaining % 2) == 0;
                                            conclusion 0;
                                        }
                                    } and {
                                        both {
                                            intro();
                                            intro();
                                            intro();
                                            intro();
                                            intro();
                                            intro();
                                            assumption();
                                        } and {
                                            both {
                                                intro();
                                                intro();
                                                intro();
                                                intro();
                                                intro();
                                                intro();
                                                intro();
                                                both {
                                                    arithmetic_certificate signed_int32 {
                                                        premise 0: 0 <= __rust_mir_17_remaining => 0 <= __rust_mir_17_remaining;
                                                        premise 1: __rust_mir_17_remaining <= 4 => __rust_mir_17_remaining <= 4;
                                                        premise 2: 4 <= (8 - __rust_mir_8_remaining) => 4 <= (8 - __rust_mir_8_remaining);
                                                        premise 3: (8 - __rust_mir_8_remaining) <= 8 => (8 - __rust_mir_8_remaining) <= 8;
                                                        interval_atom (0) (0) (0);
                                                        interval_from_affine_direct 2 ((8 - __rust_mir_8_remaining)) (4) (2147483647);
                                                        interval_from_affine_direct 3 ((8 - __rust_mir_8_remaining)) (-2147483648) (8);
                                                        interval_intersect 5, 6 (4) (8);
                                                        interval_from_affine_direct 0 (__rust_mir_17_remaining) (0) (2147483647);
                                                        interval_from_affine_direct 1 (__rust_mir_17_remaining) (-2147483648) (4);
                                                        interval_intersect 8, 9 (0) (4);
                                                        interval_subtract 7, 10 7 (0) (8);
                                                        interval_compare 4, 11 le => 0 <= ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining);
                                                        conclusion 12;
                                                    }
                                                } and {
                                                    arithmetic_certificate signed_int32 {
                                                        premise 0: 0 <= __rust_mir_17_remaining => 0 <= __rust_mir_17_remaining;
                                                        premise 1: __rust_mir_17_remaining <= 4 => __rust_mir_17_remaining <= 4;
                                                        premise 2: 4 <= (8 - __rust_mir_8_remaining) => 4 <= (8 - __rust_mir_8_remaining);
                                                        premise 3: (8 - __rust_mir_8_remaining) <= 8 => (8 - __rust_mir_8_remaining) <= 8;
                                                        interval_from_affine_direct 2 ((8 - __rust_mir_8_remaining)) (4) (2147483647);
                                                        interval_from_affine_direct 3 ((8 - __rust_mir_8_remaining)) (-2147483648) (8);
                                                        interval_intersect 4, 5 (4) (8);
                                                        interval_from_affine_direct 0 (__rust_mir_17_remaining) (0) (2147483647);
                                                        interval_from_affine_direct 1 (__rust_mir_17_remaining) (-2147483648) (4);
                                                        interval_intersect 7, 8 (0) (4);
                                                        interval_subtract 6, 9 6 (0) (8);
                                                        interval_atom (8) (8) (8);
                                                        interval_compare 10, 11 le => ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining) <= 8;
                                                        conclusion 12;
                                                    }
                                                }
                                            } and {
                                                both {
                                                    intro();
                                                    intro();
                                                    intro();
                                                    intro();
                                                    intro();
                                                    intro();
                                                    intro();
                                                    intro();
                                                    both {
                                                        arithmetic_certificate signed_int32 {
                                                            premise 0: 4 <= (8 - __rust_mir_8_remaining) => 4 <= (8 - __rust_mir_8_remaining);
                                                            conclusion 0;
                                                        }
                                                    } and {
                                                        arithmetic_certificate signed_int32 {
                                                            premise 0: (8 - __rust_mir_8_remaining) <= 8 => (8 - __rust_mir_8_remaining) <= 8;
                                                            conclusion 0;
                                                        }
                                                    }
                                                } and {
                                                    both {
                                                        arithmetic_certificate signed_int32 {
                                                            premise 0: 0 <= __rust_mir_17_remaining => 0 <= __rust_mir_17_remaining;
                                                            conclusion 0;
                                                        }
                                                    } and {
                                                        arithmetic_certificate signed_int32 {
                                                            premise 0: at(statement(226).entry, __rust_mir_17_remaining) <= at(statement(226).entry, 4) => at(statement(226).entry, __rust_mir_17_remaining) <= at(statement(226).entry, 4);
                                                            premise 1: at(statement(226).entry, ((int32)((uint32)__rust_mir_17_size))) <= at(statement(226).entry, __rust_mir_17_remaining) => at(statement(226).entry, ((int32)((uint32)__rust_mir_17_size))) <= at(statement(226).entry, __rust_mir_17_remaining);
                                                            interval_from_affine 1 (at(statement(226).entry, __rust_mir_17_remaining)) (2) (2147483647);
                                                            interval_from_affine 0 (at(statement(226).entry, __rust_mir_17_remaining)) (-2147483648) (4);
                                                            interval_intersect 2, 3 (2) (4);
                                                            interval_atom (2) (2) (2);
                                                            interval_subtract 4, 5 4 (0) (2);
                                                            trivial => -1 <= 0;
                                                            affine_conclusion 7 6 => __rust_mir_17_remaining < at(statement(226).entry, __rust_mir_17_remaining);
                                                            conclusion 8;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            have __rust_mir_17_remaining < 2 by {
                cases (not 0 < __rust_mir_17_remaining or not 2 <= __rust_mir_17_remaining) {
                    have __rust_mir_17_remaining <= 0 by {
                        extract(at(statement(158).entry, 0) <= at(statement(158).entry, __rust_mir_8_remaining));
                        extract(at(loop(1).exit, 0) <= at(loop(1).exit, __rust_mir_17_remaining));
                        extract(at(loop(1).exit, 0) <= at(loop(1).exit, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)));
                        extract(at(statement(158).entry, __rust_mir_8_remaining) <= at(statement(158).entry, 8));
                        extract(at(loop(1).exit, __rust_mir_17_remaining) <= at(loop(1).exit, 4));
                        extract(at(loop(1).exit, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) <= at(loop(1).exit, 8));
                        apply(int32_not_lt_implies_ge(at(statement(276).entry, 0), at(statement(276).entry, __rust_mir_17_remaining))) using {
                            not at(statement(276).entry, 0) < at(statement(276).entry, __rust_mir_17_remaining);
                        }
                        apply(int32_ge_implies_reversed_le(at(statement(276).entry, 0), at(statement(276).entry, __rust_mir_17_remaining))) using {
                            at(statement(276).entry, 0) >= at(statement(276).entry, __rust_mir_17_remaining);
                        }
                    }
                    arithmetic_certificate signed_int32 {
                        premise 0: __rust_mir_17_remaining <= 0 => __rust_mir_17_remaining <= 0;
                        trivial => -1 <= 0;
                        add 0, 1 => (__rust_mir_17_remaining + -1) <= (0 + 0);
                        conclusion 2;
                    }
                } {
                    arithmetic_certificate signed_int32 {
                        premise 0: not at(statement(276).entry, 2) <= at(statement(276).entry, __rust_mir_17_remaining) => not at(statement(276).entry, 2) <= at(statement(276).entry, __rust_mir_17_remaining);
                        conclusion 0;
                    }
                }
            }
            have (__rust_mir_17_remaining % 2) == __rust_mir_17_remaining by {
                normalize() using {
                    0 <= __rust_mir_17_remaining;
                    __rust_mir_17_remaining < 2;
                }
            }
            have __rust_mir_17_remaining == 0 by {
                extract(at(statement(158).entry, 0) <= at(statement(158).entry, __rust_mir_8_remaining));
                extract(at(loop(1).exit, 0) <= at(loop(1).exit, __rust_mir_17_remaining));
                extract(at(loop(1).exit, 0) <= at(loop(1).exit, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)));
                extract(at(statement(158).entry, __rust_mir_8_remaining) <= at(statement(158).entry, 8));
                extract(at(loop(1).exit, __rust_mir_17_remaining) <= at(loop(1).exit, 4));
                extract(at(loop(1).exit, ((8 - __rust_mir_8_remaining) - __rust_mir_17_remaining)) <= at(loop(1).exit, 8));
                rewrite(at(function.entry, __rust_mir_17_remaining) == at(function.entry, (__rust_mir_17_remaining % 2)));
                rewrite(at(loop(1).exit, (__rust_mir_17_remaining % 2)) == at(loop(1).exit, 0));
                normalize();
            }
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            have viewable(bytes[0..8]) by {
                transport(at(outer, viewable(bytes[0..8])), viewable(bytes[0..8])) using {
                    at(outer, viewable(bytes[0..8]));
                }
            }
            close_invariants by {
                extract(at(statement(158).entry, 0) <= at(statement(158).entry, __rust_mir_8_remaining));
                extract(at(statement(158).entry, __rust_mir_8_remaining) <= at(statement(158).entry, 8));
                both {
                    both {
                        arithmetic_certificate signed_int32 {
                            premise 0: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                            conclusion 0;
                        }
                    } and {
                        arithmetic_certificate signed_int32 {
                            premise 0: at(statement(158).entry, __rust_mir_8_remaining) <= at(statement(158).entry, 8) => at(statement(158).entry, __rust_mir_8_remaining) <= at(statement(158).entry, 8);
                            premise 1: at(statement(158).entry, ((int32)((uint32)__rust_mir_8_size))) <= at(statement(158).entry, __rust_mir_8_remaining) => at(statement(158).entry, ((int32)((uint32)__rust_mir_8_size))) <= at(statement(158).entry, __rust_mir_8_remaining);
                            interval_from_affine 1 (at(statement(158).entry, __rust_mir_8_remaining)) (4) (2147483647);
                            interval_from_affine 0 (at(statement(158).entry, __rust_mir_8_remaining)) (-2147483648) (8);
                            interval_intersect 2, 3 (4) (8);
                            interval_atom (4) (4) (4);
                            interval_subtract 4, 5 4 (0) (4);
                            trivial => -4 <= 0;
                            add 0, 7 => (at(statement(158).entry, __rust_mir_8_remaining) + -4) <= (at(statement(158).entry, 8) + 0);
                            affine_conclusion 8 6 => __rust_mir_8_remaining <= 8;
                            conclusion 9;
                        }
                    }
                } and {
                    both {
                        intro();
                        arithmetic_certificate signed_int32 {
                            premise 0: (__rust_mir_8_remaining % 4) == 0 => (__rust_mir_8_remaining % 4) == 0;
                            conclusion 0;
                        }
                    } and {
                        both {
                            intro();
                            intro();
                            intro();
                            assumption();
                        } and {
                            both {
                                intro();
                                intro();
                                intro();
                                intro();
                                arithmetic_certificate signed_int32 {
                                    trivial => 0 == 0;
                                    conclusion 0;
                                }
                            } and {
                                both {
                                    intro();
                                    intro();
                                    intro();
                                    intro();
                                    intro();
                                    arithmetic_certificate signed_int32 {
                                        trivial => 0 == 0;
                                        conclusion 0;
                                    }
                                } and {
                                    both {
                                        intro();
                                        intro();
                                        intro();
                                        intro();
                                        intro();
                                        intro();
                                        arithmetic_certificate signed_int32 {
                                            trivial => 0 == 0;
                                            conclusion 0;
                                        }
                                    } and {
                                        both {
                                            arithmetic_certificate signed_int32 {
                                                premise 0: 0 <= __rust_mir_8_remaining => 0 <= __rust_mir_8_remaining;
                                                conclusion 0;
                                            }
                                        } and {
                                            arithmetic_certificate signed_int32 {
                                                premise 0: at(statement(158).entry, __rust_mir_8_remaining) <= at(statement(158).entry, 8) => at(statement(158).entry, __rust_mir_8_remaining) <= at(statement(158).entry, 8);
                                                premise 1: at(statement(158).entry, ((int32)((uint32)__rust_mir_8_size))) <= at(statement(158).entry, __rust_mir_8_remaining) => at(statement(158).entry, ((int32)((uint32)__rust_mir_8_size))) <= at(statement(158).entry, __rust_mir_8_remaining);
                                                interval_from_affine 1 (at(statement(158).entry, __rust_mir_8_remaining)) (4) (2147483647);
                                                interval_from_affine 0 (at(statement(158).entry, __rust_mir_8_remaining)) (-2147483648) (8);
                                                interval_intersect 2, 3 (4) (8);
                                                interval_atom (4) (4) (4);
                                                interval_subtract 4, 5 4 (0) (4);
                                                trivial => -3 <= 0;
                                                affine_conclusion 7 6 => __rust_mir_8_remaining < at(statement(158).entry, __rust_mir_8_remaining);
                                                conclusion 8;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    have __rust_mir_8_remaining < 4 by {
        cases (not 0 < __rust_mir_8_remaining or not 4 <= __rust_mir_8_remaining) {
            have __rust_mir_8_remaining <= 0 by {
                extract(at(loop(0).exit, 0) <= at(loop(0).exit, __rust_mir_8_remaining));
                extract(at(loop(0).exit, __rust_mir_8_remaining) <= at(loop(0).exit, 8));
                apply(int32_not_lt_implies_ge(at(statement(301).entry, 0), at(statement(301).entry, __rust_mir_8_remaining))) using {
                    not at(statement(301).entry, 0) < at(statement(301).entry, __rust_mir_8_remaining);
                }
                apply(int32_ge_implies_reversed_le(at(statement(301).entry, 0), at(statement(301).entry, __rust_mir_8_remaining))) using {
                    at(statement(301).entry, 0) >= at(statement(301).entry, __rust_mir_8_remaining);
                }
            }
            arithmetic_certificate signed_int32 {
                premise 0: __rust_mir_8_remaining <= 0 => __rust_mir_8_remaining <= 0;
                trivial => -3 <= 0;
                add 0, 1 => (__rust_mir_8_remaining + -3) <= (0 + 0);
                conclusion 2;
            }
        } {
            arithmetic_certificate signed_int32 {
                premise 0: not at(statement(301).entry, 4) <= at(statement(301).entry, __rust_mir_8_remaining) => not at(statement(301).entry, 4) <= at(statement(301).entry, __rust_mir_8_remaining);
                conclusion 0;
            }
        }
    }
    have (__rust_mir_8_remaining % 4) == __rust_mir_8_remaining by {
        normalize() using {
            0 <= __rust_mir_8_remaining;
            __rust_mir_8_remaining < 4;
        }
    }
    have __rust_mir_8_remaining == 0 by {
        extract(at(loop(0).exit, 0) <= at(loop(0).exit, __rust_mir_8_remaining));
        extract(at(loop(0).exit, __rust_mir_8_remaining) <= at(loop(0).exit, 8));
        rewrite(at(function.entry, __rust_mir_8_remaining) == at(function.entry, (__rust_mir_8_remaining % 4)));
        rewrite(at(loop(0).exit, (__rust_mir_8_remaining % 4)) == at(loop(0).exit, 0));
        normalize();
    }
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have result == 0u64 by {
        rewrite(at(function.entry, bytes_len == 8u64));
        normalize();
    }
    have forall (k: int32) { 0 <= k and k < 8 implies bytes[k] == old(bytes[k]) } by {
        enumerate();
    }
    assumption();
    assumption();
}

uint64 empty_array_len() { ensures result == 0u64; } by { execute(); simp(); }
uint64 medium_array_len() { ensures result == 1024u64; } by { execute(); simp(); }
uint64 large_array_len() { ensures result == 1000000u64; } by { execute(); simp(); }
uint8 array_read(uint64 index) {
    requires index < 8u64;
    ensures result == 7;
} by { execute(); simp(); }
