import click::integer;

spec enum WriteAttempt {
    Attempt(List<uint8>, int32),
}

abstract resource stream(file: void*) {
    field write_history: List<WriteAttempt>;
}

function write_requests(history: List<WriteAttempt>) -> List<List<uint8>>
    decreases history
{
    match history {
        List::Nil => List<List<uint8>>::Nil,
        List::Cons(attempt, tail) => match attempt {
            WriteAttempt::Attempt(bytes, _) =>
                List<List<uint8>>::Cons(bytes, stdio::write_requests(tail)),
        },
    }
}

// Decimal rendering as C's `printf` family writes an integer: the fewest
// digits that write it, most significant first, so zero is "0". A digit is
// its ASCII character, `'0'` through `'9'`. The C front end states each
// `snprintf` call's output with these functions
// (docs/reference/language/c.md#formatted-output).

// 10 to the power `e`, for the exponents of a 64-bit value's digits.
function pow10(e: uint64) -> uint64 {
    (if e == 0u64 { 1u64 } else { 0u64 }) + (if e == 1u64 { 10u64 } else { 0u64 }) + (if e == 2u64 { 100u64 } else { 0u64 }) + (if e == 3u64 { 1000u64 } else { 0u64 }) + (if e == 4u64 { 10000u64 } else { 0u64 }) + (if e == 5u64 { 100000u64 } else { 0u64 }) + (if e == 6u64 { 1000000u64 } else { 0u64 }) + (if e == 7u64 { 10000000u64 } else { 0u64 }) + (if e == 8u64 { 100000000u64 } else { 0u64 }) + (if e == 9u64 { 1000000000u64 } else { 0u64 }) + (if e == 10u64 { 10000000000u64 } else { 0u64 }) + (if e == 11u64 { 100000000000u64 } else { 0u64 }) + (if e == 12u64 { 1000000000000u64 } else { 0u64 }) + (if e == 13u64 { 10000000000000u64 } else { 0u64 }) + (if e == 14u64 { 100000000000000u64 } else { 0u64 }) + (if e == 15u64 { 1000000000000000u64 } else { 0u64 }) + (if e == 16u64 { 10000000000000000u64 } else { 0u64 }) + (if e == 17u64 { 100000000000000000u64 } else { 0u64 }) + (if e == 18u64 { 1000000000000000000u64 } else { 0u64 }) + (if e == 19u64 { 10000000000000000000u64 } else { 0u64 })
}

// The number of decimal digits of `v`.
function decimal_length(v: uint64) -> uint64 {
    1u64 + (if v < 10u64 { 0u64 } else { 1u64 }) + (if v < 100u64 { 0u64 } else { 1u64 }) + (if v < 1000u64 { 0u64 } else { 1u64 }) + (if v < 10000u64 { 0u64 } else { 1u64 }) + (if v < 100000u64 { 0u64 } else { 1u64 }) + (if v < 1000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000000000000u64 { 0u64 } else { 1u64 })
}

// The character of `v`'s `k`th decimal digit, counting from the most
// significant. Past the last digit, at `k >= decimal_length(v)`, it is `'0'`.
function decimal_digit(v: uint64, k: uint64) -> uint8 {
    if k < stdio::decimal_length(v) {
        (48u64 + v / stdio::pow10(stdio::decimal_length(v) - 1u64 - k) % 10u64) as uint8
    } else {
        48u8
    }
}

// The characters `%*u` writes for `v` in a field of `width`: `v`'s digits,
// preceded by enough `pad` characters (`'0'` for a `0` flag, else `' '`)
// to fill the field.
function padded_length(v: uint64, width: uint64) -> uint64 {
    if stdio::decimal_length(v) < width { width } else { stdio::decimal_length(v) }
}

function padded_digit(v: uint64, width: uint64, pad: uint8, k: uint64) -> uint8 {
    if to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v)) {
        pad
    } else {
        stdio::decimal_digit(v, k - (stdio::padded_length(v, width) - stdio::decimal_length(v)))
    }
}

// The magnitude of a signed `int`, exact even for `INT_MIN`.
function magnitude(v: int32) -> uint64 {
    if v < 0 { (0i64 - v as int64) as uint64 } else { v as uint64 }
}

// The characters `%d` writes for `v`: a `'-'` before a negative value's
// digits.
function signed_length(v: int32) -> uint64 {
    if v < 0 { 1u64 + stdio::decimal_length(stdio::magnitude(v)) } else { stdio::decimal_length(stdio::magnitude(v)) }
}

function signed_digit(v: int32, k: uint64) -> uint8 {
    if v < 0 {
        if k == 0u64 { 45u8 } else { stdio::decimal_digit(stdio::magnitude(v), k - 1u64) }
    } else {
        stdio::decimal_digit(stdio::magnitude(v), k)
    }
}

theorem pow10_0() {
    ensures stdio::pow10(0u64) == 1u64 by {
        unfold(stdio::pow10(0u64));
        solve();
    }
}

theorem pow10_1() {
    ensures stdio::pow10(1u64) == 10u64 by {
        unfold(stdio::pow10(1u64));
        solve();
    }
}

theorem pow10_2() {
    ensures stdio::pow10(2u64) == 100u64 by {
        unfold(stdio::pow10(2u64));
        solve();
    }
}

theorem pow10_3() {
    ensures stdio::pow10(3u64) == 1000u64 by {
        unfold(stdio::pow10(3u64));
        solve();
    }
}

theorem pow10_4() {
    ensures stdio::pow10(4u64) == 10000u64 by {
        unfold(stdio::pow10(4u64));
        solve();
    }
}

theorem pow10_5() {
    ensures stdio::pow10(5u64) == 100000u64 by {
        unfold(stdio::pow10(5u64));
        solve();
    }
}

theorem pow10_6() {
    ensures stdio::pow10(6u64) == 1000000u64 by {
        unfold(stdio::pow10(6u64));
        solve();
    }
}

theorem pow10_7() {
    ensures stdio::pow10(7u64) == 10000000u64 by {
        unfold(stdio::pow10(7u64));
        solve();
    }
}

theorem pow10_8() {
    ensures stdio::pow10(8u64) == 100000000u64 by {
        unfold(stdio::pow10(8u64));
        solve();
    }
}

theorem pow10_9() {
    ensures stdio::pow10(9u64) == 1000000000u64 by {
        unfold(stdio::pow10(9u64));
        solve();
    }
}

// Every exponent `pow10` names has a power that is not zero. The cases are
// decided one at a time, from the largest down.
theorem pow10_nonzero(e: uint64) {
    requires e < 20u64;
    ensures stdio::pow10(e) != 0u64 by {
        unfold(stdio::pow10(e));
        if e == 19u64 {
            normalize() using { e == 19u64; };
        } else {
            have e < 19u64 by { solve() using { e < 20u64; not (e == 19u64); }; }
            if e == 18u64 {
                normalize() using { e == 18u64; };
            } else {
                have e < 18u64 by { solve() using { e < 19u64; not (e == 18u64); }; }
                if e == 17u64 {
                    normalize() using { e == 17u64; };
                } else {
                    have e < 17u64 by { solve() using { e < 18u64; not (e == 17u64); }; }
                    if e == 16u64 {
                        normalize() using { e == 16u64; };
                    } else {
                        have e < 16u64 by { solve() using { e < 17u64; not (e == 16u64); }; }
                        if e == 15u64 {
                            normalize() using { e == 15u64; };
                        } else {
                            have e < 15u64 by { solve() using { e < 16u64; not (e == 15u64); }; }
                            if e == 14u64 {
                                normalize() using { e == 14u64; };
                            } else {
                                have e < 14u64 by { solve() using { e < 15u64; not (e == 14u64); }; }
                                if e == 13u64 {
                                    normalize() using { e == 13u64; };
                                } else {
                                    have e < 13u64 by { solve() using { e < 14u64; not (e == 13u64); }; }
                                    if e == 12u64 {
                                        normalize() using { e == 12u64; };
                                    } else {
                                        have e < 12u64 by { solve() using { e < 13u64; not (e == 12u64); }; }
                                        if e == 11u64 {
                                            normalize() using { e == 11u64; };
                                        } else {
                                            have e < 11u64 by { solve() using { e < 12u64; not (e == 11u64); }; }
                                            if e == 10u64 {
                                                normalize() using { e == 10u64; };
                                            } else {
                                                have e < 10u64 by { solve() using { e < 11u64; not (e == 10u64); }; }
                                                if e == 9u64 {
                                                    normalize() using { e == 9u64; };
                                                } else {
                                                    have e < 9u64 by { solve() using { e < 10u64; not (e == 9u64); }; }
                                                    if e == 8u64 {
                                                        normalize() using { e == 8u64; };
                                                    } else {
                                                        have e < 8u64 by { solve() using { e < 9u64; not (e == 8u64); }; }
                                                        if e == 7u64 {
                                                            normalize() using { e == 7u64; };
                                                        } else {
                                                            have e < 7u64 by { solve() using { e < 8u64; not (e == 7u64); }; }
                                                            if e == 6u64 {
                                                                normalize() using { e == 6u64; };
                                                            } else {
                                                                have e < 6u64 by { solve() using { e < 7u64; not (e == 6u64); }; }
                                                                if e == 5u64 {
                                                                    normalize() using { e == 5u64; };
                                                                } else {
                                                                    have e < 5u64 by { solve() using { e < 6u64; not (e == 5u64); }; }
                                                                    if e == 4u64 {
                                                                        normalize() using { e == 4u64; };
                                                                    } else {
                                                                        have e < 4u64 by { solve() using { e < 5u64; not (e == 4u64); }; }
                                                                        if e == 3u64 {
                                                                            normalize() using { e == 3u64; };
                                                                        } else {
                                                                            have e < 3u64 by { solve() using { e < 4u64; not (e == 3u64); }; }
                                                                            if e == 2u64 {
                                                                                normalize() using { e == 2u64; };
                                                                            } else {
                                                                                have e < 2u64 by { solve() using { e < 3u64; not (e == 2u64); }; }
                                                                                if e == 1u64 {
                                                                                    normalize() using { e == 1u64; };
                                                                                } else {
                                                                                    have e < 1u64 by { solve() using { e < 2u64; not (e == 1u64); }; }
                                                                                    have e == 0u64 by { solve() using { e < 1u64; }; }
                                                                                    normalize() using { e == 0u64; };
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
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

theorem decimal_length_1(v: uint64) {
    requires v < 10u64;
    ensures stdio::decimal_length(v) == 1u64 by {
        have v < 10u64 by { solve(); }
        have v < 100u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100u64)); }
        have v < 1000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000u64)); }
        have v < 10000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000u64)); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10u64; }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100u64; }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000u64; }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        normalize();
    }
}

theorem decimal_length_2(v: uint64) {
    requires 10u64 <= v;
    requires v < 100u64;
    ensures stdio::decimal_length(v) == 2u64 by {
        have not (v < 10u64) by { solve(); }
        have v < 100u64 by { solve(); }
        have v < 1000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000u64)); }
        have v < 10000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000u64)); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100u64; }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000u64; }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        normalize();
    }
}

theorem decimal_length_3(v: uint64) {
    requires 100u64 <= v;
    requires v < 1000u64;
    ensures stdio::decimal_length(v) == 3u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 100u64, v)); }
        have not (v < 100u64) by { solve(); }
        have v < 1000u64 by { solve(); }
        have v < 10000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000u64)); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000u64; }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        normalize();
    }
}

theorem decimal_length_4(v: uint64) {
    requires 1000u64 <= v;
    requires v < 10000u64;
    ensures stdio::decimal_length(v) == 4u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 1000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 1000u64, v)); }
        have not (v < 1000u64) by { solve(); }
        have v < 10000u64 by { solve(); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        normalize();
    }
}

theorem decimal_length_5(v: uint64) {
    requires 10000u64 <= v;
    requires v < 100000u64;
    ensures stdio::decimal_length(v) == 5u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 10000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 10000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 10000u64, v)); }
        have not (v < 10000u64) by { solve(); }
        have v < 100000u64 by { solve(); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        normalize();
    }
}

theorem decimal_length_6(v: uint64) {
    requires 100000u64 <= v;
    requires v < 1000000u64;
    ensures stdio::decimal_length(v) == 6u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 100000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 100000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 100000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 100000u64, v)); }
        have not (v < 100000u64) by { solve(); }
        have v < 1000000u64 by { solve(); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        normalize();
    }
}

theorem decimal_length_7(v: uint64) {
    requires 1000000u64 <= v;
    requires v < 10000000u64;
    ensures stdio::decimal_length(v) == 7u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 1000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 1000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 1000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 1000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 1000000u64, v)); }
        have not (v < 1000000u64) by { solve(); }
        have v < 10000000u64 by { solve(); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        normalize();
    }
}

theorem decimal_length_8(v: uint64) {
    requires 10000000u64 <= v;
    requires v < 100000000u64;
    ensures stdio::decimal_length(v) == 8u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 10000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 10000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 10000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 10000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 10000000u64, v)); }
        have not (v < 1000000u64) by { apply(integer::uint64_less_equal_transitive(1000000u64, 10000000u64, v)); }
        have not (v < 10000000u64) by { solve(); }
        have v < 100000000u64 by { solve(); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000000u64); }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        normalize();
    }
}

theorem decimal_length_9(v: uint64) {
    requires 100000000u64 <= v;
    requires v < 1000000000u64;
    ensures stdio::decimal_length(v) == 9u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 100000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 100000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 100000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 100000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 100000000u64, v)); }
        have not (v < 1000000u64) by { apply(integer::uint64_less_equal_transitive(1000000u64, 100000000u64, v)); }
        have not (v < 10000000u64) by { apply(integer::uint64_less_equal_transitive(10000000u64, 100000000u64, v)); }
        have not (v < 100000000u64) by { solve(); }
        have v < 1000000000u64 by { solve(); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000000u64); }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000000u64); }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        normalize();
    }
}

theorem decimal_length_10(v: uint64) {
    requires 1000000000u64 <= v;
    requires v < 10000000000u64;
    ensures stdio::decimal_length(v) == 10u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 1000000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 1000000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 1000000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 1000000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 1000000000u64, v)); }
        have not (v < 1000000u64) by { apply(integer::uint64_less_equal_transitive(1000000u64, 1000000000u64, v)); }
        have not (v < 10000000u64) by { apply(integer::uint64_less_equal_transitive(10000000u64, 1000000000u64, v)); }
        have not (v < 100000000u64) by { apply(integer::uint64_less_equal_transitive(100000000u64, 1000000000u64, v)); }
        have not (v < 1000000000u64) by { solve(); }
        have v < 10000000000u64 by { solve(); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 10000000000000000000u64)); }
        unfold(stdio::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000000u64); }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000000u64); }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000000000u64); }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }), 1u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }), 0u64);
        normalize();
    }
}

// Where `k` names one of `v`'s digits, the power of ten that selects it is
// not zero, so the digit's division by it has a value.
theorem decimal_digit_power_nonzero(v: uint64, k: uint64) {
    requires k < stdio::decimal_length(v);
    ensures stdio::pow10(stdio::decimal_length(v) - 1u64 - k) != 0u64 by {
        have stdio::decimal_length(v) <= 20u64 by {
            unfold(stdio::decimal_length(v));
            solve();
        }
        have (stdio::decimal_length(v) - 1u64 - k) as uint64 < 20u64 by { solve(); }
        apply(stdio::pow10_nonzero(stdio::decimal_length(v) - 1u64 - k));
    }
}

// The `k`th digit of an `n`-digit value; for a known `n` and `k`, `pow10_e`
// gives the power of ten it divides by.
theorem decimal_digit_of_length(v: uint64, n: uint64, k: uint64) {
    requires stdio::decimal_length(v) == n;
    requires k < n;
    ensures stdio::decimal_digit(v, k) == (48u64 + v / stdio::pow10(n - 1u64 - k) % 10u64) as uint8 by {
        unfold(stdio::decimal_digit(v, k));
        rewrite(stdio::decimal_length(v), n);
        normalize() using { k < n; };
    }
}

// Every digit is a character from '0' up, so none is the terminator.
theorem decimal_digit_lower_bound(v: uint64, k: uint64) {
    ensures 48u8 <= stdio::decimal_digit(v, k) by {
        if k < stdio::decimal_length(v) {
            apply(stdio::decimal_digit_power_nonzero(v, k));
            unfold(stdio::decimal_digit(v, k));
            have 48u8 <= (48u64 + v / stdio::pow10(stdio::decimal_length(v) - 1u64 - k) % 10u64) as uint8;
            normalize() using { k < stdio::decimal_length(v); };
            known();
        } else {
            unfold(stdio::decimal_digit(v, k));
            normalize() using { not (k < stdio::decimal_length(v)); };
        }
    }
}

theorem padded_digit_lower_bound(v: uint64, width: uint64, k: uint64) {
    ensures 48u8 <= stdio::padded_digit(v, width, 48u8, k) by {
        unfold(stdio::padded_digit(v, width, 48u8, k));
        if to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v)) {
            normalize() using { to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v)); };
        } else {
            apply(stdio::decimal_digit_lower_bound(v, k - (stdio::padded_length(v, width) - stdio::decimal_length(v))));
            solve() using { not (to_integer(k) < to_integer(stdio::padded_length(v, width) - stdio::decimal_length(v))); 48u8 <= stdio::decimal_digit(v, k - (stdio::padded_length(v, width) - stdio::decimal_length(v))); };
        }
    }
}
