verifying "chunks.rs";

fn cover(bytes: &[u8]) -> usize {
    views bytes[0..bytes.len()];
    ensures result == bytes.len() % 4u64;
    ensures forall (k: uint64) {
        k < bytes.len() implies bytes[k] == old(bytes[k])
    };
} by {
    have bytes.len() % 4u64 <= bytes.len() by normalize();
    execute_until(loop(0));
    have iter_remaining == bytes.len() - bytes.len() % 4u64;
    have (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64;
    have iter_remaining % 4u64 == 0u64 by {
        rewrite(iter_remaining == bytes.len() - bytes.len() % 4u64); simp();
    }
    have (bytes.len() - bytes.len() % 4u64) - iter_remaining == 0u64 by {
        arithmetic() using {
            iter_remaining == bytes.len() - bytes.len() % 4u64;
            bytes.len() % 4u64 <= bytes.len();
        }
    }
    have iter_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) - iter_remaining) by {
        rewrite((bytes.len() - bytes.len() % 4u64) - iter_remaining == 0u64); simp();
    }
    loop {
        decreases iter_remaining;
        views bytes[0..bytes.len()];
        invariant iter_size == 4u64;
        invariant iter_tail_len == bytes.len() % 4u64;
        invariant tail_len == iter_tail_len;
        invariant iter_tail == bytes + (bytes.len() - bytes.len() % 4u64);
        invariant tail == iter_tail;
        invariant iter_remaining <= bytes.len() - bytes.len() % 4u64;
        invariant iter_remaining % 4u64 == 0u64;
        invariant iter_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) - iter_remaining);
        preserve by {
            have 4u64 <= iter_remaining;
            mark iteration;
            have (bytes.len() - bytes.len() % 4u64) - iter_remaining < bytes.len() by {
                arithmetic() using {
                    4u64 <= iter_remaining;
                    iter_remaining <= (bytes.len() - bytes.len() % 4u64);
                    bytes.len() % 4u64 <= bytes.len();
                }
            }
            have ((bytes.len() - bytes.len() % 4u64) - iter_remaining) + 3u64 < bytes.len() by {
                arithmetic() using {
                    4u64 <= iter_remaining;
                    iter_remaining <= (bytes.len() - bytes.len() % 4u64);
                    bytes.len() % 4u64 <= bytes.len();
                }
            }
            have 4 + to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) <= to_integer(bytes.len()) by {
                apply(uint64_less_equal_to_integer(iter_remaining, bytes.len() - bytes.len() % 4u64)) using {
                    iter_remaining <= bytes.len() - bytes.len() % 4u64;
                }
                apply(uint64_less_equal_to_integer(bytes.len() % 4u64, bytes.len())) using {
                    bytes.len() % 4u64 <= bytes.len();
                }
                apply(uint64_subtract_to_integer(bytes.len() - bytes.len() % 4u64, iter_remaining)) using {
                    to_integer(iter_remaining) <= to_integer(bytes.len() - bytes.len() % 4u64);
                }
                apply(uint64_subtract_to_integer(bytes.len(), bytes.len() % 4u64)) using {
                    to_integer(bytes.len() % 4u64) <= to_integer(bytes.len());
                }
                apply(uint64_less_equal_to_integer(4u64, iter_remaining)) using { 4u64 <= iter_remaining; }
                apply(uint64_to_integer_bounds(bytes.len() % 4u64));
                arithmetic() using {
                    to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) == to_integer(bytes.len() - bytes.len() % 4u64) - to_integer(iter_remaining);
                    to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64);
                    4 <= to_integer(iter_remaining);
                    0 <= to_integer(bytes.len() % 4u64);
                }
            }
            have 3 + to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) <= to_integer(bytes.len()) by {
                arithmetic() using { 4 + to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) <= to_integer(bytes.len()); }
            }
            have 3 + to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) < to_integer(bytes.len()) by {
                arithmetic() using { 4 + to_integer((bytes.len() - bytes.len() % 4u64) - iter_remaining) <= to_integer(bytes.len()); }
            }
            execute_until(read(1)); step();
            have iter_remaining == at(iteration, iter_remaining) - 4u64;
            have (at(iteration, iter_remaining) - 4u64) % 4u64 == at(iteration, iter_remaining % 4u64) by {
                normalize() using { 4u64 <= at(iteration, iter_remaining); }
            }
            have iter_remaining % 4u64 == 0u64 by {
                rewrite(iter_remaining == at(iteration, iter_remaining) - 4u64);
                rewrite((at(iteration, iter_remaining) - 4u64) % 4u64 == at(iteration, iter_remaining % 4u64));
                simp();
            }
            have iter_remaining <= (bytes.len() - bytes.len() % 4u64) by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 4u64;
                    4u64 <= at(iteration, iter_remaining);
                    at(iteration, iter_remaining) <= (bytes.len() - bytes.len() % 4u64);
                    bytes.len() % 4u64 <= bytes.len();
                }
            }
            have (bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining) <= 18446744073709551611u64 by {
                arithmetic() using {
                    4u64 <= at(iteration, iter_remaining);
                    at(iteration, iter_remaining) <= (bytes.len() - bytes.len() % 4u64);
                    bytes.len() % 4u64 <= bytes.len();
                }
            }
            have at(iteration, iter_cursor) + 4 == bytes + (((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining)) + 4u64) by {
                arithmetic() using {
                    at(iteration, iter_cursor) == bytes + ((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining));
                    (bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining) <= 18446744073709551611u64;
                }
            }
            have (bytes.len() - bytes.len() % 4u64) - iter_remaining == ((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining)) + 4u64 by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 4u64;
                    4u64 <= at(iteration, iter_remaining);
                    at(iteration, iter_remaining) <= (bytes.len() - bytes.len() % 4u64);
                    bytes.len() % 4u64 <= bytes.len();
                }
            }
            have iter_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) - iter_remaining) by {
                rewrite((bytes.len() - bytes.len() % 4u64) - iter_remaining == ((bytes.len() - bytes.len() % 4u64) - at(iteration, iter_remaining)) + 4u64);
                simp();
            }
            have iter_remaining < at(iteration, iter_remaining) by {
                arithmetic() using {
                    iter_remaining == at(iteration, iter_remaining) - 4u64;
                    4u64 <= at(iteration, iter_remaining);
                }
            }
            execute_until(back_edge());
            close_invariants();
        }
    }
    have iter_remaining < 4u64 by {
        cases {
            not (0u64 < iter_remaining) => {
                arithmetic() using { not 0u64 < iter_remaining; }
            }
            not (4u64 <= iter_remaining) => { assumption(); }
        }
    }
    have iter_remaining % 4u64 == iter_remaining by {
        normalize() using { iter_remaining < 4u64; }
    }
    have iter_remaining == 0u64;
    have iter_cursor == iter_tail;
    execute();
    have forall (k: uint64) {
        k < bytes.len() implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); simp(); }
    simp();
}
