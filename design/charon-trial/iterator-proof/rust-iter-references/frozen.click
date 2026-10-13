verifying "sum.rs";
function prefix(bytes: const uint8*, end: int32) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer((int32)bytes[k])
    })
}
int32 sum(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len <= 1000u64;
    views bytes[0..(int32)(uint32)bytes_len];
    ensures to_integer(result) == old(prefix(bytes, (int32)(uint32)bytes_len));
} by {
    execute_until(statement(9));
    have 0 <= (int32)(uint32)bytes_len by { simp(); }
    have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
        transport(at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
            at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len]));
            0 <= (int32)(uint32)bytes_len;
        }
    }
    have prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining)) == 0 by {
        peel(prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining))) using {
            0 >= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining);
        } simp();
    }
    have to_integer(total) == 0 by {
        simp();
    }
    have to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining)) by {
        arithmetic() using {
            to_integer(total) == 0;
            prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining)) == 0;
        }
    }
    // This sidecar chooses an input-prefix invariant; the iterator supplies
    // its remaining slice and cursor, without a processed-count variable.
    loop {
        decreases __rust_iter_3_5_remaining;
        views bytes[0..(int32)(uint32)bytes_len];
        invariant viewable(bytes[0..(int32)(uint32)bytes_len]);
        invariant bytes_len <= 1000u64;
        invariant 0 <= __rust_iter_3_5_remaining and __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len;
        invariant 0 <= (int32)(uint32)bytes_len and 1000 >= (int32)(uint32)bytes_len;
        invariant __rust_iter_3_5_cursor == bytes + ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining);
        invariant 0 <= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) and 1000 >= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining);
        invariant 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining));
        invariant to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining));
        preserve by {
            have 0 < __rust_iter_3_5_remaining by { arithmetic() using { 0 <= __rust_iter_3_5_remaining; not (__rust_iter_3_5_remaining == 0); } }
            have 0 <= __rust_iter_3_5_remaining - 1 by { arithmetic() using { 0 < __rust_iter_3_5_remaining; } }
            have 0 <= to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining)) by {
                apply(int32_less_equal_to_integer(0, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining))) using {
                    0 <= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining);
                }
            }
            have to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining)) <= 1000 by {
                apply(int32_less_equal_to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining), 1000)) using {
                    1000 >= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining);
                }
            }
            have to_integer(total) <= 255000 by {
                arithmetic() using {
                    to_integer(total) <= 255 * to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining));
                    to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining)) <= 1000;
                }
            }
            have __rust_iter_3_5_remaining - 1 <= (int32)(uint32)bytes_len by {
                apply(int32_nonnegative_predecessor_upper_bound(__rust_iter_3_5_remaining, (int32)(uint32)bytes_len)) using {
                    0 <= __rust_iter_3_5_remaining;
                    __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len;
                }
            }
            execute_until(statement(15));
            have 0 <= __rust_iter_3_5_remaining by { simp(); }
            have __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len by { simp(); }
            have ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) < (int32)(uint32)bytes_len by { arithmetic() using {
                at(statement(10).entry, 0 < __rust_iter_3_5_remaining);
                at(statement(10).entry, __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len);
                0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
            } }
            have 0 <= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) by {
                arithmetic() using {
                    at(statement(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(statement(10).entry, __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have 0 <= (int32)(uint32)bytes_len by { simp(); }
            have ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) == at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining) by {
                arithmetic() using {
                    at(statement(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(statement(10).entry, __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have __rust_iter_3_5_item == bytes + at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining) by { simp(); }
            have __rust_iter_3_5_item == bytes + ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) by {
                rewrite(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) == at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining));
                simp();
            }
            execute_until(statement(23));
            have bytes + ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) == __rust_iter_3_5_item by { simp(); }
            have 0 <= __rust_checked_1 and 255 >= __rust_checked_1 by { simp(); }
            have 0 <= (int32)load_uint8(__rust_iter_3_5_item) and 255 >= (int32)load_uint8(__rust_iter_3_5_item) by { simp(); }
            have ((int32)load_uint8(__rust_iter_3_5_item)) == (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)] by {
                rewrite(__rust_iter_3_5_item == bytes + ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1));
                simp();
            }
            have 0 <= (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)] and 255 >= (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)] by {
                rewrite(bytes + ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) == __rust_iter_3_5_item); simp();
            }
            have defined((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) by {
                apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)bytes_len, __rust_iter_3_5_remaining)) using {
                    0 <= __rust_iter_3_5_remaining;
                    __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len;
                } simp();
            }
            have 1 <= (int32)(uint32)bytes_len - __rust_iter_3_5_remaining by {
                arithmetic() using {
                    at(statement(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(statement(10).entry, __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have defined((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) by {
                apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)bytes_len - __rust_iter_3_5_remaining, 1)) using {
                    0 <= 1;
                    1 <= (int32)(uint32)bytes_len - __rust_iter_3_5_remaining;
                } simp();
            }
            have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
                transport(at(statement(10).entry, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
                    at(statement(10).entry, viewable(bytes[0..(int32)(uint32)bytes_len]));
                    0 <= (int32)(uint32)bytes_len;
                }
            }
            have defined(bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) by {
                transport(viewable(bytes[0..(int32)(uint32)bytes_len]), defined(bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)])) using {
                    viewable(bytes[0..(int32)(uint32)bytes_len]);
                    defined((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1);
                    0 <= (int32)(uint32)bytes_len;
                    0 <= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1);
                    ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) < (int32)(uint32)bytes_len;
                }
            }
            have 0 <= to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) by {
                apply(int32_less_equal_to_integer(0, (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)])) using {
                    0 <= (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)];
                }
            }
            have to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255 by {
                apply(int32_less_equal_to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)], 255)) using {
                    255 >= (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)];
                }
            }
            have to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) >= -2147483648 by {
                arithmetic() using {
                    0 <= to_integer(total);
                    0 <= to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                }
            }
            have to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 2147483647 by {
                arithmetic() using {
                    to_integer(total) <= 255000;
                    to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255;
                }
            }
            have defined(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) by {
                apply(int32_add_defined_by_integer_bounds(total, (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)])) using {
                    to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) >= -2147483648;
                    to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 2147483647;
                } simp();
            }
            have to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) == to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) by {
                apply(int32_add_to_integer(total, (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)])) using {
                    defined(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                }
            }
            have 1000 >= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) by {
                arithmetic() using {
                    at(statement(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(statement(10).entry, __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) by {
                rewrite(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) == at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining)); simp();
            }
            have to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) == at(statement(10).entry, to_integer((int32)(uint32)bytes_len - __rust_iter_3_5_remaining)) by {
                rewrite(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) == at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining)); simp();
            }
            have to_integer(total) <= 255 * to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) by {
                arithmetic() using {
                    at(statement(10).entry, to_integer(total) <= 255 * to_integer((int32)(uint32)bytes_len - __rust_iter_3_5_remaining));
                    to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) == at(statement(10).entry, to_integer((int32)(uint32)bytes_len - __rust_iter_3_5_remaining));
                }
            }
            have (((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) < 2147483647 by {
                apply(int32_le_lt_transitive(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1), 1000, 2147483647)) using {
                    1000 >= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1);
                    1000 < 2147483647;
                }
            }
            have prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) == prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) by {
                peel(prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1)) using {
                    0 <= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1);
                    (((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) < 2147483647;
                }
                simp();
            }
            have to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) == prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) by {
                arithmetic() using {
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) == to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                    to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1));
                    prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) == prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                }
            }
            have defined(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) by {
                apply(int32_increment_below_max_is_defined(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1))) using {
                    (((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) < 2147483647;
                } simp();
            }
            have to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) == to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) + 1 by {
                apply(int32_add_to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1), 1)) using {
                    defined(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1);
                }
            }
            have 0 <= to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) by {
                arithmetic() using {
                    0 <= to_integer(total);
                    0 <= to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                }
            }
            have 0 <= to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) by {
                arithmetic() using {
                    0 <= to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) == to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                }
            }
            have to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255 * (to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) + 1) by {
                arithmetic() using {
                    to_integer(total) <= 255 * to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1));
                    to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255;
                }
            }
            have to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255 * to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) by {
                arithmetic() using {
                    to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255 * (to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) + 1);
                    to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) == to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)) + 1;
                }
            }
            have to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255 * to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) by {
                arithmetic() using {
                    to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255 * to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1);
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) == to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                }
            }
            have ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) == ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1 by {
                arithmetic() using {
                    at(statement(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(statement(10).entry, __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining) < 2147483647 by {
                apply(int32_le_lt_transitive(at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining), 1000, 2147483647)) using {
                    at(statement(10).entry, 1000 >= ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining));
                    1000 < 2147483647;
                }
            }
            have __rust_iter_3_5_item + 1 == bytes + (at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining) + 1) by {
                arithmetic() using {
                    __rust_iter_3_5_item == bytes + at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining);
                    at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining) < 2147483647;
                }
            }
            have ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) == at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining) + 1 by {
                arithmetic() using {
                    at(statement(10).entry, 0 < __rust_iter_3_5_remaining);
                    at(statement(10).entry, __rust_iter_3_5_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have __rust_iter_3_5_cursor == bytes + ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) by {
                rewrite(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) == at(statement(10).entry, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining) + 1);
                simp();
            }
            have to_integer((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) == to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) by {
                rewrite(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) == ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1); simp();
            }
            have to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255 * to_integer((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) by {
                arithmetic() using {
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255 * to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1);
                    to_integer((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) == to_integer(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1);
                }
            }
            have prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) == prefix(bytes, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining) by {
                rewrite(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) == ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1); simp();
            }
            have ((int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) == (int32)load_uint8(__rust_iter_3_5_item) by { simp(); }
            have defined(total + (int32)load_uint8(__rust_iter_3_5_item)) by {
                rewrite(((int32)load_uint8(__rust_iter_3_5_item)) == (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]); simp();
            }
            // Connect Rust's captured addition operands to the mathematical sum.
            have __rust_checked_1 == (int32)load_uint8(__rust_iter_3_5_item) by { simp(); }
            have __rust_checked_0 == total by { simp(); }
            have defined(__rust_checked_0 + __rust_checked_1) by { simp(); }
            have to_integer(__rust_checked_0 + __rust_checked_1) == to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) by {
                rewrite(__rust_checked_0 == total);
                rewrite(__rust_checked_1 == (int32)load_uint8(__rust_iter_3_5_item));
                rewrite(((int32)load_uint8(__rust_iter_3_5_item)) == (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]); simp();
            }
            have 0 <= to_integer(__rust_checked_0 + __rust_checked_1) by {
                arithmetic() using {
                    to_integer(__rust_checked_0 + __rust_checked_1) == to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                    0 <= to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                }
            }
            have to_integer(__rust_checked_0 + __rust_checked_1) <= 255 * to_integer((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) by {
                arithmetic() using {
                    to_integer(__rust_checked_0 + __rust_checked_1) == to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) <= 255 * to_integer((int32)(uint32)bytes_len - __rust_iter_3_5_remaining);
                }
            }
            have to_integer(__rust_checked_0 + __rust_checked_1) == prefix(bytes, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining) by {
                arithmetic() using {
                    to_integer(__rust_checked_0 + __rust_checked_1) == to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]);
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1)]) == prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1);
                    prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining - 1) + 1) == prefix(bytes, (int32)(uint32)bytes_len - __rust_iter_3_5_remaining);
                }
            }
            step();
            have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
                transport(at(statement(23).entry, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
                    at(statement(23).entry, viewable(bytes[0..(int32)(uint32)bytes_len]));
                    0 <= (int32)(uint32)bytes_len;
                }
            }
            close_invariants();
        }
    }
    have __rust_iter_3_5_remaining == 0 by { simp(); }
    have ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) == (int32)(uint32)bytes_len by { simp(); }
    have prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining)) == prefix(bytes, (int32)(uint32)bytes_len) by {
        rewrite(((int32)(uint32)bytes_len - __rust_iter_3_5_remaining) == (int32)(uint32)bytes_len); simp();
    }
    have to_integer(total) == prefix(bytes, (int32)(uint32)bytes_len) by {
        arithmetic() using {
            to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining));
            prefix(bytes, ((int32)(uint32)bytes_len - __rust_iter_3_5_remaining)) == prefix(bytes, (int32)(uint32)bytes_len);
        }
    }
    execute();
    simp();
}
