verifying "chunks.rs";
uint64 tail(const uint8* bytes, uint64 bytes_len, uint64 size) {
    requires bytes_len <= 2147483647u64;
    requires size != 0u64;
    ensures result == bytes_len % size;
} by { execute(); simp(); }

uint64 walk(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len <= 1000u64;
    views bytes[0..(int32)(uint32)bytes_len];
    ensures result == bytes_len % 4u64;
    ensures forall (k: int32) {
        0 <= k and k < (int32)(uint32)bytes_len implies bytes[k] == old(bytes[k])
    };
} by {
    have bytes_len % 4u64 <= bytes_len by { normalize(); }
    have bytes_len - bytes_len % 4u64 <= bytes_len by { normalize() using { bytes_len % 4u64 <= bytes_len; } }
    have bytes_len - bytes_len % 4u64 <= 1000u64 by { normalize() using { bytes_len - bytes_len % 4u64 <= bytes_len; bytes_len <= 1000u64; } }
    have bytes_len - bytes_len % 4u64 <= 2147483647u64 by { normalize() using { bytes_len - bytes_len % 4u64 <= 1000u64; } }
    have 0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64) by { normalize() using { bytes_len - bytes_len % 4u64 <= 2147483647u64; } }
    have ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 1000 by { simp(); }
    have bytes_len <= 2147483647u64 by { normalize() using { bytes_len <= 1000u64; } }
    have ((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= (int32)(uint32)bytes_len by { normalize() using { bytes_len - bytes_len % 4u64 <= bytes_len; bytes_len <= 2147483647u64; } }
    execute_until(loop(0));
    have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
        transport(at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
            at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len]));
            0 <= (int32)(uint32)bytes_len;
        }
    }
    have bytes_len <= 2147483647u64 by { normalize() using { bytes_len <= 1000u64; } }
    have (((int32)(uint32)(bytes_len - bytes_len % 4u64)) % 4) == 0 by { normalize() using { bytes_len <= 2147483647u64; } }
    have iter_remaining == (int32)(uint32)(bytes_len - bytes_len % 4u64) by { simp(); }
    have iter_remaining % 4 == 0 by {
        rewrite(iter_remaining == (int32)(uint32)(bytes_len - bytes_len % 4u64)); simp();
    }
    loop {
    decreases iter_remaining;
    views bytes[0..((int32)((uint32)bytes_len))];
    invariant viewable(bytes[0..((int32)((uint32)bytes_len))]);
    invariant bytes_len <= 1000u64;
    invariant 0 <= ((int32)((uint32)bytes_len)) and ((int32)((uint32)bytes_len)) <= 1000;
    invariant 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) and ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= ((int32)((uint32)bytes_len));
    invariant ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000;
    invariant iter_size == 4u64;
    invariant iter_tail_len == (bytes_len % 4u64);
    invariant tail_len == iter_tail_len;
    invariant iter_tail == (bytes + ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))));
    invariant tail == iter_tail;
    invariant 0 <= iter_remaining and iter_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))));
    invariant (iter_remaining % 4) == 0;
    invariant iter_cursor == (bytes + (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining));
    invariant 0 <= (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) and (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) <= 1000;
    initialize by {
        have viewable(bytes[0..((int32)((uint32)bytes_len))]) by {
            rewrite(at(function.entry, iter_remaining) == at(function.entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))));
            assumption();
        }
        have bytes_len <= 1000u64 by {
            rewrite(at(function.entry, iter_remaining) == at(function.entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))));
            assumption();
        }
        have 0 <= ((int32)((uint32)bytes_len)) and ((int32)((uint32)bytes_len)) <= 1000 by {
            both {
                assumption();
            } and {
                normalize() using {
                    at(function.entry, bytes_len) <= at(function.entry, 1000u64);
                    at(function.entry, 0) == at(function.entry, 0);
                }
            }
        }
        have 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) and ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= ((int32)((uint32)bytes_len)) by {
            both {
                assumption();
            } and {
                assumption();
            }
        }
        have ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000 by {
            normalize() using {
                at(function.entry, (bytes_len - (bytes_len % 4u64))) <= at(function.entry, 1000u64);
                at(function.entry, 0) == at(function.entry, 0);
            }
        }
        have iter_size == 4u64 by {
            normalize();
        }
        have iter_tail_len == (bytes_len % 4u64) by {
            normalize();
        }
        have tail_len == iter_tail_len by {
            normalize();
        }
        have iter_tail == (bytes + ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) by {
            normalize();
        }
        have tail == iter_tail by {
            normalize();
        }
        have 0 <= iter_remaining and iter_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) by {
            both {
                assumption();
            } and {
                normalize();
            }
        }
        have (iter_remaining % 4) == 0 by {
            normalize() using {
                at(function.entry, bytes_len) <= at(function.entry, 2147483647u64);
            }
        }
        have iter_cursor == (bytes + (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)) by {
            normalize();
        }
        have 0 <= (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) and (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) <= 1000 by {
            split();
        }
    }
    preserve by {
        have 4 <= iter_remaining by {
            assumption();
        }
        mark iteration;
        have ((((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) + 4) <= ((int32)((uint32)bytes_len)) by {
            arithmetic_certificate signed_int32 {
                premise 0: 4 <= iter_remaining => 4 <= iter_remaining;
                premise 1: ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= ((int32)((uint32)bytes_len)) => ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= ((int32)((uint32)bytes_len));
                premise 2: ((int32)((uint32)bytes_len)) <= 1000 => ((int32)((uint32)bytes_len)) <= 1000;
                premise 3: 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) => 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))));
                add 1, 2 => (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) + ((int32)((uint32)bytes_len))) <= (((int32)((uint32)bytes_len)) + 1000);
                interval_from_affine 3 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (0) (2147483647);
                interval_from_affine 4 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (-2147483648) (1000);
                interval_intersect 5, 6 (0) (1000);
                interval_from_affine 0 (iter_remaining) (4) (2147483647);
                interval_subtract 7, 8 7 (-2147483647) (996);
                interval_atom (4) (4) (4);
                interval_add_bounded 9, 10 (-2147483643) (1000);
                add 0, 1 => (4 + ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) <= (iter_remaining + ((int32)((uint32)bytes_len)));
                affine_conclusion 12 11 => ((((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) + 4) <= ((int32)((uint32)bytes_len));
                conclusion 13;
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
        have viewable(bytes[0..((int32)((uint32)bytes_len))]) by {
            transport(at(iteration, viewable(bytes[0..((int32)((uint32)bytes_len))])), viewable(bytes[0..((int32)((uint32)bytes_len))])) using {
                at(iteration, viewable(bytes[0..((int32)((uint32)bytes_len))]));
                0 <= ((int32)((uint32)bytes_len));
            }
        }
        have iter_remaining == (at(iteration, iter_remaining) - 4) by {
            normalize();
        }
        have ((at(iteration, iter_remaining) - 4) % 4) == at(iteration, (iter_remaining % 4)) by {
            normalize() using {
                at(iteration, 4 <= iter_remaining);
            }
        }
        have (iter_remaining % 4) == 0 by {
            rewrite(iter_remaining == (at(iteration, iter_remaining) - 4));
            rewrite(((at(iteration, iter_remaining) - 4) % 4) == at(iteration, (iter_remaining % 4)));
            assumption();
        }
        have 0 <= iter_remaining by {
            arithmetic_certificate signed_int32 {
                premise 0: at(iteration, 4 <= iter_remaining) => at(iteration, 4 <= iter_remaining);
                interval_from_affine 0 (at(iteration, iter_remaining)) (4) (2147483647);
                interval_atom (4) (4) (4);
                interval_subtract 1, 2 1 (0) (2147483643);
                affine_conclusion 0 3 => 0 <= iter_remaining;
                conclusion 4;
            }
        }
        have iter_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) by {
            arithmetic_certificate signed_int32 {
                premise 0: at(iteration, 4 <= iter_remaining) => at(iteration, 4 <= iter_remaining);
                premise 1: at(iteration, iter_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) => at(iteration, iter_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))));
                premise 2: ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000 => ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000;
                add 1, 2 => (at(iteration, iter_remaining) + ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) <= (at(iteration, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 1000);
                interval_from_affine 0 (at(iteration, iter_remaining)) (4) (2147483647);
                interval_from_affine 3 (at(iteration, iter_remaining)) (-2147483648) (1000);
                interval_intersect 4, 5 (4) (1000);
                interval_atom (4) (4) (4);
                interval_subtract 6, 7 6 (0) (996);
                trivial => -4 <= 0;
                add 1, 9 => (at(iteration, iter_remaining) + -4) <= (at(iteration, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 0);
                affine_conclusion 10 8 => iter_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))));
                conclusion 11;
            }
        }
        have iter_cursor == (at(iteration, iter_cursor) + 4) by {
            normalize();
        }
        have (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) == (at(iteration, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)) + 4) by {
            arithmetic_certificate signed_int32 {
                premise 0: iter_remaining == (at(iteration, iter_remaining) - 4) => iter_remaining == (at(iteration, iter_remaining) - 4);
                premise 1: at(iteration, 4 <= iter_remaining) => at(iteration, 4 <= iter_remaining);
                premise 2: at(iteration, iter_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) => at(iteration, iter_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))));
                premise 3: 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) => 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))));
                premise 4: ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000 => ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000;
                interval_from_affine 3 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (0) (2147483647);
                interval_from_affine 4 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (-2147483648) (1000);
                interval_intersect 5, 6 (0) (1000);
                add 2, 4 => (at(iteration, iter_remaining) + ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) <= (at(iteration, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 1000);
                interval_from_affine 1 (at(iteration, iter_remaining)) (4) (2147483647);
                interval_from_affine 8 (at(iteration, iter_remaining)) (-2147483648) (1000);
                interval_intersect 9, 10 (4) (1000);
                interval_atom (4) (4) (4);
                interval_subtract 11, 12 11 (0) (996);
                interval_subtract 7, 13 7 (-996) (1000);
                interval_subtract 7, 11 7 (-1000) (996);
                interval_add_bounded 15, 12 (-996) (1000);
                affine_conclusion_pair 0 14 16 => (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) == (at(iteration, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)) + 4);
                conclusion 17;
            }
        }
        have (at(iteration, iter_cursor) + 4) == (bytes + (at(iteration, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)) + 4)) by {
            arithmetic_certificate special {
                premise 0: at(iteration, iter_cursor == (bytes + (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining))) => at(iteration, iter_cursor == (bytes + (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)));
                premise 1: at(iteration, 0 <= (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)) => at(iteration, 0 <= (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining));
                premise 2: at(iteration, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) <= 1000) => at(iteration, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) <= 1000);
                pointer_translation relation 0 bounds [1, 2] => (at(iteration, iter_cursor) + 4) == (bytes + (at(iteration, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)) + 4));
                conclusion 0;
            }
        }
        have iter_cursor == (bytes + (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)) by {
            rewrite((((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining) == (at(iteration, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)) + 4));
            assumption();
        }
        close_invariants by {
            extract(((int32)((uint32)bytes_len)) <= 1000);
            extract(at(statement(122).entry, 0) <= at(statement(122).entry, iter_remaining));
            extract(at(statement(122).entry, iter_remaining) <= at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))));
            extract(at(statement(122).entry, 0) <= at(statement(122).entry, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)));
            extract(at(statement(122).entry, (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) - iter_remaining)) <= at(statement(122).entry, 1000));
            both {
                normalize();
            } and {
                both {
                    intro();
                    normalize();
                } and {
                    both {
                        intro();
                        intro();
                        both {
                            arithmetic_certificate signed_int32 {
                                premise 0: 0 <= iter_remaining => 0 <= iter_remaining;
                                conclusion 0;
                            }
                        } and {
                            arithmetic_certificate signed_int32 {
                                premise 0: iter_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) => iter_remaining <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))));
                                conclusion 0;
                            }
                        }
                    } and {
                        both {
                            intro();
                            intro();
                            intro();
                            arithmetic_certificate signed_int32 {
                                premise 0: (iter_remaining % 4) == 0 => (iter_remaining % 4) == 0;
                                conclusion 0;
                            }
                        } and {
                            both {
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
                                    both {
                                        arithmetic_certificate signed_int32 {
                                            premise 0: 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) => 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))));
                                            premise 1: ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000 => ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000;
                                            premise 2: at(statement(122).entry, iter_remaining) <= at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) => at(statement(122).entry, iter_remaining) <= at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))));
                                            premise 3: at(statement(122).entry, ((int32)((uint32)iter_size))) <= at(statement(122).entry, iter_remaining) => at(statement(122).entry, ((int32)((uint32)iter_size))) <= at(statement(122).entry, iter_remaining);
                                            interval_from_affine 0 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (0) (2147483647);
                                            interval_from_affine 1 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (-2147483648) (1000);
                                            interval_intersect 4, 5 (0) (1000);
                                            add 2, 1 => (at(statement(122).entry, iter_remaining) + ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) <= (at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 1000);
                                            interval_from_affine 3 (at(statement(122).entry, iter_remaining)) (4) (2147483647);
                                            interval_from_affine 7 (at(statement(122).entry, iter_remaining)) (-2147483648) (1000);
                                            interval_intersect 8, 9 (4) (1000);
                                            interval_atom (4) (4) (4);
                                            interval_subtract 10, 11 10 (0) (996);
                                            interval_subtract 6, 12 6 (-996) (1000);
                                            trivial => -4 <= 0;
                                            add 2, 14 => (at(statement(122).entry, iter_remaining) + -4) <= (at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 0);
                                            affine_conclusion 15 13 => 0 <= (__rust_mir_6_remaining - iter_remaining);
                                            conclusion 16;
                                        }
                                    } and {
                                        arithmetic_certificate signed_int32 {
                                            premise 0: 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) => 0 <= ((int32)((uint32)(bytes_len - (bytes_len % 4u64))));
                                            premise 1: ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000 => ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000;
                                            premise 2: at(statement(122).entry, iter_remaining) <= at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) => at(statement(122).entry, iter_remaining) <= at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))));
                                            premise 3: at(statement(122).entry, ((int32)((uint32)iter_size))) <= at(statement(122).entry, iter_remaining) => at(statement(122).entry, ((int32)((uint32)iter_size))) <= at(statement(122).entry, iter_remaining);
                                            interval_from_affine 0 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (0) (2147483647);
                                            interval_from_affine 1 (((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) (-2147483648) (1000);
                                            interval_intersect 4, 5 (0) (1000);
                                            add 2, 1 => (at(statement(122).entry, iter_remaining) + ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) <= (at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 1000);
                                            interval_from_affine 3 (at(statement(122).entry, iter_remaining)) (4) (2147483647);
                                            interval_from_affine 7 (at(statement(122).entry, iter_remaining)) (-2147483648) (1000);
                                            interval_intersect 8, 9 (4) (1000);
                                            interval_atom (4) (4) (4);
                                            interval_subtract 10, 11 10 (0) (996);
                                            interval_subtract 6, 12 6 (-996) (1000);
                                            add 1, 3 => (((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) + at(statement(122).entry, ((int32)((uint32)iter_size)))) <= (1000 + at(statement(122).entry, iter_remaining));
                                            affine_conclusion 14 13 => (__rust_mir_6_remaining - iter_remaining) <= 1000;
                                            conclusion 15;
                                        }
                                    }
                                } and {
                                    both {
                                        arithmetic_certificate signed_int32 {
                                            premise 0: 0 <= iter_remaining => 0 <= iter_remaining;
                                            conclusion 0;
                                        }
                                    } and {
                                        arithmetic_certificate signed_int32 {
                                            premise 0: ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000 => ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))) <= 1000;
                                            premise 1: at(statement(122).entry, iter_remaining) <= at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) => at(statement(122).entry, iter_remaining) <= at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64)))));
                                            premise 2: at(statement(122).entry, ((int32)((uint32)iter_size))) <= at(statement(122).entry, iter_remaining) => at(statement(122).entry, ((int32)((uint32)iter_size))) <= at(statement(122).entry, iter_remaining);
                                            add 1, 0 => (at(statement(122).entry, iter_remaining) + ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) <= (at(statement(122).entry, ((int32)((uint32)(bytes_len - (bytes_len % 4u64))))) + 1000);
                                            interval_from_affine 2 (at(statement(122).entry, iter_remaining)) (4) (2147483647);
                                            interval_from_affine 3 (at(statement(122).entry, iter_remaining)) (-2147483648) (1000);
                                            interval_intersect 4, 5 (4) (1000);
                                            interval_atom (4) (4) (4);
                                            interval_subtract 6, 7 6 (0) (996);
                                            trivial => -3 <= 0;
                                            affine_conclusion 9 8 => iter_remaining < at(statement(122).entry, iter_remaining);
                                            conclusion 10;
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
    have iter_remaining < 4 by {
        cases(not (0 < iter_remaining) or not (4 <= iter_remaining)) {
            have iter_remaining <= 0 by { simp(); }
            arithmetic() using { iter_remaining <= 0; }
        } { simp(); }
    }
    have iter_remaining % 4 == iter_remaining by { normalize() using { 0 <= iter_remaining; iter_remaining < 4; } }
    have iter_remaining == 0 by { simp(); }
    have iter_cursor == iter_tail by { simp(); }
    execute();
    have forall (k: int32) {
        0 <= k and k < (int32)(uint32)bytes_len implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); simp(); }
    simp();
}

uint64 next_len(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 8u64;
    ensures result == 4u64;
} by { execute(); simp(); }

uint8 tail_byte(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 7u64;
    views bytes[0..7];
    ensures result == old(bytes[4]);
} by {
    have ((int32)(uint32)(bytes_len - bytes_len % 4u64)) == 4 by { rewrite(bytes_len == 7u64); simp(); }
    have ((int32)(uint32)(bytes_len - bytes_len % 4u64)) != 0 by { simp(); }
    execute(); simp();
}
