import "bounds.click";

// The vector index is a logical observation of existing remaining-byte state.
// No runtime counter is added, and no loop invariant is assumed established.
function adler_lane_vectors_consumed(total: int32, remaining: int32) -> Integer {
    truncating_quotient(to_integer(total) - to_integer(remaining), 4)
}

theorem adler_lane_iterator_observations(total: int32, remaining: int32) {
    requires 0 <= remaining;
    requires remaining <= total;
    requires total <= 22208;
    ensures 0 <= to_integer(remaining) by apply(int32_less_equal_to_integer(0, remaining)) using { 0 <= remaining; };
    ensures to_integer(remaining) <= to_integer(total) by apply(int32_less_equal_to_integer(remaining, total)) using { remaining <= total; };
    ensures to_integer(total) <= 22208 by apply(int32_less_equal_to_integer(total, 22208)) using { total <= 22208; };
}

theorem adler_lane_iterator_consumed_bounds(total: int32, remaining: int32) {
    requires 0 <= remaining;
    requires remaining <= total;
    requires total <= 22208;
    ensures 0 <= to_integer(total) - to_integer(remaining) by {
        have to_integer(remaining) <= to_integer(total) by apply(adler_lane_iterator_observations(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        arithmetic() using { to_integer(remaining) <= to_integer(total); }
    }
    ensures to_integer(total) - to_integer(remaining) <= 22208 by {
        have 0 <= to_integer(remaining) by apply(adler_lane_iterator_observations(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have to_integer(total) <= 22208 by apply(adler_lane_iterator_observations(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        arithmetic() using { 0 <= to_integer(remaining); to_integer(total) <= 22208; }
    }
}

theorem adler_lane_iterator_count_bounds(consumed: Integer, divisor: Integer) {
    requires 0 <= consumed;
    requires consumed <= 22208;
    requires 4 <= divisor;
    requires divisor <= 4;
    requires divisor != 0;
    ensures 0 <= truncating_quotient(consumed, divisor) by {
        arithmetic_certificate rules {
            premise 0: 0 <= consumed => 0 <= consumed;
            premise 1: consumed <= 22208 => consumed <= 22208;
            premise 2: 4 <= divisor => 4 <= divisor;
            premise 3: divisor <= 4 => divisor <= 4;
            integer_division_bounds bounds [0, 1, 2, 3] => 0 <= truncating_quotient(consumed, divisor);
            conclusion 0;
        }
    }
    ensures truncating_quotient(consumed, divisor) <= 5552 by {
        arithmetic_certificate rules {
            premise 0: 0 <= consumed => 0 <= consumed;
            premise 1: consumed <= 22208 => consumed <= 22208;
            premise 2: 4 <= divisor => 4 <= divisor;
            premise 3: divisor <= 4 => divisor <= 4;
            integer_division_bounds bounds [0, 1, 2, 3] => truncating_quotient(consumed, divisor) <= 5552;
            conclusion 0;
        }
    }
}

theorem adler_lane_iterator_index_bounds(total: int32, remaining: int32) {
    requires 0 <= remaining;
    requires remaining <= total;
    requires total <= 22208;
    ensures 0 <= adler_lane_vectors_consumed(total, remaining) by {
        have 0 <= to_integer(total) - to_integer(remaining) by apply(adler_lane_iterator_consumed_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have to_integer(total) - to_integer(remaining) <= 22208 by apply(adler_lane_iterator_consumed_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        unfold(adler_lane_vectors_consumed(total, remaining));
        apply(adler_lane_iterator_count_bounds(to_integer(total) - to_integer(remaining), 4)) using { 0 <= to_integer(total) - to_integer(remaining); to_integer(total) - to_integer(remaining) <= 22208; }
    }
    ensures adler_lane_vectors_consumed(total, remaining) <= 5552 by {
        have 0 <= to_integer(total) - to_integer(remaining) by apply(adler_lane_iterator_consumed_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have to_integer(total) - to_integer(remaining) <= 22208 by apply(adler_lane_iterator_consumed_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        unfold(adler_lane_vectors_consumed(total, remaining));
        apply(adler_lane_iterator_count_bounds(to_integer(total) - to_integer(remaining), 4)) using { 0 <= to_integer(total) - to_integer(remaining); to_integer(total) - to_integer(remaining) <= 22208; }
    }
}

theorem adler_lane_iterator_initial(total: int32) {
    ensures adler_lane_vectors_consumed(total, total) == 0 by {
        have to_integer(total) - to_integer(total) == 0 by arithmetic();
        unfold(adler_lane_vectors_consumed(total, total));
        rewrite(to_integer(total) - to_integer(total) == 0); normalize();
    }
}

theorem adler_lane_iterator_next_defined(total: int32, remaining: int32) {
    requires 4 <= remaining;
    requires remaining <= total;
    requires total <= 22208;
    ensures defined(remaining - 4) by {
        have remaining <= 22208 by arithmetic() using { remaining <= total; total <= 22208; };
        simp() using { 4 <= remaining; remaining <= 22208; }
    }
}

theorem adler_lane_iterator_count_before_next(consumed: Integer, divisor: Integer) {
    requires 0 <= consumed;
    requires consumed <= 22204;
    requires 4 <= divisor;
    requires divisor <= 4;
    requires divisor != 0;
    ensures truncating_quotient(consumed, divisor) <= 5551 by {
        arithmetic_certificate rules {
            premise 0: 0 <= consumed => 0 <= consumed;
            premise 1: consumed <= 22204 => consumed <= 22204;
            premise 2: 4 <= divisor => 4 <= divisor;
            premise 3: divisor <= 4 => divisor <= 4;
            integer_division_bounds bounds [0, 1, 2, 3] => truncating_quotient(consumed, divisor) <= 5551;
            conclusion 0;
        }
    }
}

theorem adler_lane_iterator_index_before_next(total: int32, remaining: int32) {
    requires 0 <= remaining;
    requires 4 <= remaining;
    requires remaining <= total;
    requires total <= 22208;
    ensures adler_lane_vectors_consumed(total, remaining) <= 5551 by {
        have 0 <= to_integer(total) - to_integer(remaining) by apply(adler_lane_iterator_consumed_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have 4 <= to_integer(remaining) by apply(int32_less_equal_to_integer(4, remaining)) using { 4 <= remaining; };
        have to_integer(total) <= 22208 by apply(adler_lane_iterator_observations(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have to_integer(total) - to_integer(remaining) <= 22204 by arithmetic() using { 4 <= to_integer(remaining); to_integer(total) <= 22208; };
        unfold(adler_lane_vectors_consumed(total, remaining));
        apply(adler_lane_iterator_count_before_next(to_integer(total) - to_integer(remaining), 4)) using { 0 <= to_integer(total) - to_integer(remaining); to_integer(total) - to_integer(remaining) <= 22204; }
    }
}

theorem adler_lane_iterator_quotient_shift(consumed: Integer, increment: Integer) {
    requires 0 <= consumed;
    requires 0 <= increment;
    ensures truncating_quotient(consumed + 4 * increment, 4) == truncating_quotient(consumed, 4) + increment by {
        arithmetic_certificate rules {
            premise 0: 0 <= consumed => 0 <= consumed;
            premise 1: 0 <= increment => 0 <= increment;
            integer_quotient_shift bounds [0, 1] => truncating_quotient(consumed + 4 * increment, 4) == truncating_quotient(consumed, 4) + increment;
            conclusion 0;
        }
    }
}

theorem adler_lane_iterator_successor(total: int32, remaining: int32) {
    requires 0 <= remaining;
    requires remaining <= total;
    requires total <= 22208;
    requires defined(remaining - 4);
    ensures adler_lane_vectors_consumed(total, remaining - 4) == adler_lane_vectors_consumed(total, remaining) + 1 by {
        have to_integer(remaining - 4) == to_integer(remaining) - 4 by apply(int32_subtract_to_integer(remaining, 4)) using { defined(remaining - 4); };
        have 0 <= to_integer(total) - to_integer(remaining) by apply(adler_lane_iterator_consumed_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have to_integer(total) - (to_integer(remaining) - 4) == (to_integer(total) - to_integer(remaining)) + 4 * 1 by arithmetic();
        unfold(adler_lane_vectors_consumed(total, remaining - 4));
        unfold(adler_lane_vectors_consumed(total, remaining));
        rewrite(to_integer(remaining - 4) == to_integer(remaining) - 4);
        rewrite(to_integer(total) - (to_integer(remaining) - 4) == (to_integer(total) - to_integer(remaining)) + 4 * 1);
        apply(adler_lane_iterator_quotient_shift(to_integer(total) - to_integer(remaining), 1)) using { 0 <= to_integer(total) - to_integer(remaining); }
    }
}

// Compose the native lane updates with the index observed at the iterator head.
theorem adler_lane_iterator_native_step(total: int32, remaining: int32, a: uint32, b: uint32, byte: uint32) {
    requires 0 <= remaining;
    requires 4 <= remaining;
    requires remaining <= total;
    requires total <= 22208;
    requires 0 <= to_integer(a);
    requires to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
    requires 0 <= to_integer(b);
    requires to_integer(b) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining));
    requires 0 <= to_integer(byte);
    requires to_integer(byte) <= 255;
    ensures ((int64)a + (int64)byte) <= 4294967295i64 by {
        have 0 <= adler_lane_vectors_consumed(total, remaining) by apply(adler_lane_iterator_index_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) <= 5551 by apply(adler_lane_iterator_index_before_next(total, remaining)) using { 0 <= remaining; 4 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) < 5552 by arithmetic() using { adler_lane_vectors_consumed(total, remaining) <= 5551; };
        apply(adler_lane_native_a_step(adler_lane_vectors_consumed(total, remaining), a, byte)) using {
            0 <= adler_lane_vectors_consumed(total, remaining); adler_lane_vectors_consumed(total, remaining) < 5552;
            0 <= to_integer(a); to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
            0 <= to_integer(byte); to_integer(byte) <= 255;
        }
    }
    ensures ((int64)b + (int64)(a + byte)) <= 4294967295i64 by {
        have 0 <= adler_lane_vectors_consumed(total, remaining) by apply(adler_lane_iterator_index_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) <= 5551 by apply(adler_lane_iterator_index_before_next(total, remaining)) using { 0 <= remaining; 4 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) < 5552 by arithmetic() using { adler_lane_vectors_consumed(total, remaining) <= 5551; };
        apply(adler_lane_native_b_step(adler_lane_vectors_consumed(total, remaining), a, b, byte)) using {
            0 <= adler_lane_vectors_consumed(total, remaining); adler_lane_vectors_consumed(total, remaining) < 5552;
            0 <= to_integer(a); to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
            0 <= to_integer(b); to_integer(b) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining));
            0 <= to_integer(byte); to_integer(byte) <= 255;
        }
    }
    ensures to_integer(a + byte) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining) + 1) by {
        have 0 <= adler_lane_vectors_consumed(total, remaining) by apply(adler_lane_iterator_index_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) <= 5551 by apply(adler_lane_iterator_index_before_next(total, remaining)) using { 0 <= remaining; 4 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) < 5552 by arithmetic() using { adler_lane_vectors_consumed(total, remaining) <= 5551; };
        apply(adler_lane_native_a_step(adler_lane_vectors_consumed(total, remaining), a, byte)) using {
            0 <= adler_lane_vectors_consumed(total, remaining); adler_lane_vectors_consumed(total, remaining) < 5552;
            0 <= to_integer(a); to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
            0 <= to_integer(byte); to_integer(byte) <= 255;
        }
    }
    ensures to_integer(b + (a + byte)) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining) + 1) by {
        have 0 <= adler_lane_vectors_consumed(total, remaining) by apply(adler_lane_iterator_index_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) <= 5551 by apply(adler_lane_iterator_index_before_next(total, remaining)) using { 0 <= remaining; 4 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) < 5552 by arithmetic() using { adler_lane_vectors_consumed(total, remaining) <= 5551; };
        apply(adler_lane_native_b_step(adler_lane_vectors_consumed(total, remaining), a, b, byte)) using {
            0 <= adler_lane_vectors_consumed(total, remaining); adler_lane_vectors_consumed(total, remaining) < 5552;
            0 <= to_integer(a); to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
            0 <= to_integer(b); to_integer(b) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining));
            0 <= to_integer(byte); to_integer(byte) <= 255;
        }
    }
}

theorem adler_lane_iterator_successor_ceilings(total: int32, remaining: int32) {
    requires 0 <= remaining;
    requires remaining <= total;
    requires total <= 22208;
    requires defined(remaining - 4);
    ensures adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining - 4)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining) + 1) by {
        have adler_lane_vectors_consumed(total, remaining - 4) == adler_lane_vectors_consumed(total, remaining) + 1 by apply(adler_lane_iterator_successor(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; defined(remaining - 4); };
        unfold(adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining - 4)));
        unfold(adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining) + 1));
        rewrite(adler_lane_vectors_consumed(total, remaining - 4) == adler_lane_vectors_consumed(total, remaining) + 1); normalize();
    }
    ensures adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining - 4)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining) + 1) by {
        have adler_lane_vectors_consumed(total, remaining - 4) == adler_lane_vectors_consumed(total, remaining) + 1 by apply(adler_lane_iterator_successor(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; defined(remaining - 4); };
        unfold(adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining - 4)));
        unfold(adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining) + 1));
        unfold(adler_lane_triangle(adler_lane_vectors_consumed(total, remaining - 4)));
        unfold(adler_lane_triangle(adler_lane_vectors_consumed(total, remaining) + 1));
        rewrite(adler_lane_vectors_consumed(total, remaining - 4) == adler_lane_vectors_consumed(total, remaining) + 1); normalize();
    }
}

theorem adler_lane_iterator_native_preservation(total: int32, remaining: int32, a: uint32, b: uint32, byte: uint32) {
    requires 0 <= remaining;
    requires 4 <= remaining;
    requires remaining <= total;
    requires total <= 22208;
    requires 0 <= to_integer(a);
    requires to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
    requires 0 <= to_integer(b);
    requires to_integer(b) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining));
    requires 0 <= to_integer(byte);
    requires to_integer(byte) <= 255;
    ensures to_integer(a + byte) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining - 4)) by {
        have to_integer(a + byte) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining) + 1) by apply(adler_lane_iterator_native_step(total, remaining, a, b, byte)) using {
                0 <= remaining; 4 <= remaining; remaining <= total; total <= 22208;
                0 <= to_integer(a); to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
                0 <= to_integer(b); to_integer(b) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining));
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        have defined(remaining - 4) by apply(adler_lane_iterator_next_defined(total, remaining)) using { 4 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining - 4)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining) + 1) by apply(adler_lane_iterator_successor_ceilings(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; defined(remaining - 4); };
        rewrite(adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining - 4)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining) + 1)); simp();
    }
    ensures to_integer(b + (a + byte)) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining - 4)) by {
        have to_integer(b + (a + byte)) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining) + 1) by apply(adler_lane_iterator_native_step(total, remaining, a, b, byte)) using {
                0 <= remaining; 4 <= remaining; remaining <= total; total <= 22208;
                0 <= to_integer(a); to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
                0 <= to_integer(b); to_integer(b) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining));
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        have defined(remaining - 4) by apply(adler_lane_iterator_next_defined(total, remaining)) using { 4 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining - 4)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining) + 1) by apply(adler_lane_iterator_successor_ceilings(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; defined(remaining - 4); };
        rewrite(adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining - 4)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining) + 1)); simp();
    }
}

theorem adler_lane_iterator_boundaries() {
    ensures adler_lane_vectors_consumed(0, 0) == 0 by { unfold(adler_lane_vectors_consumed(0, 0)); normalize(); }
    ensures adler_lane_vectors_consumed(3, 0) == 0 by { unfold(adler_lane_vectors_consumed(3, 0)); normalize(); }
    ensures adler_lane_vectors_consumed(4, 0) == 1 by { unfold(adler_lane_vectors_consumed(4, 0)); normalize(); }
    ensures adler_lane_vectors_consumed(8, 4) == 1 by { unfold(adler_lane_vectors_consumed(8, 4)); normalize(); }
    ensures adler_lane_vectors_consumed(22204, 0) == 5551 by { unfold(adler_lane_vectors_consumed(22204, 0)); normalize(); }
    ensures adler_lane_vectors_consumed(22208, 4) == 5551 by { unfold(adler_lane_vectors_consumed(22208, 4)); normalize(); }
    ensures adler_lane_vectors_consumed(22208, 0) == 5552 by { unfold(adler_lane_vectors_consumed(22208, 0)); normalize(); }
}

// Initialization after construction or MOD reduction uses only the real lengths.
theorem adler_lane_iterator_reduced_initial(total: int32, a: uint32, b: uint32) {
    requires to_integer(a) <= 65520;
    requires to_integer(b) <= 65520;
    ensures to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, total)) by {
        apply(adler_lane_iterator_initial(total));
        apply(adler_lane_initial_ceiling());
        rewrite(adler_lane_vectors_consumed(total, total) == 0);
        rewrite(adler_lane_a_ceiling(0) == 65520); simp();
    }
    ensures to_integer(b) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, total)) by {
        apply(adler_lane_iterator_initial(total));
        apply(adler_lane_initial_ceiling());
        rewrite(adler_lane_vectors_consumed(total, total) == 0);
        rewrite(adler_lane_b_ceiling(0) == 65520); simp();
    }
}

// Match both Integer-sum preconditions of the unchanged AddAssign helper.
theorem adler_lane_iterator_add_contracts(total: int32, remaining: int32, a: uint32, b: uint32, byte: uint32) {
    requires 0 <= remaining;
    requires 4 <= remaining;
    requires remaining <= total;
    requires total <= 22208;
    requires 0 <= to_integer(a);
    requires to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
    requires 0 <= to_integer(b);
    requires to_integer(b) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining));
    requires 0 <= to_integer(byte);
    requires to_integer(byte) <= 255;
    ensures to_integer(a) + to_integer(byte) <= 4294967295 by {
        have 0 <= adler_lane_vectors_consumed(total, remaining) by apply(adler_lane_iterator_index_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) <= 5551 by apply(adler_lane_iterator_index_before_next(total, remaining)) using { 0 <= remaining; 4 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) < 5552 by arithmetic() using { adler_lane_vectors_consumed(total, remaining) <= 5551; };
        apply(adler_lane_native_a_sum_fits(adler_lane_vectors_consumed(total, remaining), a, byte)) using {
            0 <= adler_lane_vectors_consumed(total, remaining); adler_lane_vectors_consumed(total, remaining) < 5552;
            0 <= to_integer(a); to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
            0 <= to_integer(byte); to_integer(byte) <= 255;
        }
    }
    ensures to_integer(b) + to_integer(a + byte) <= 4294967295 by {
        have 0 <= adler_lane_vectors_consumed(total, remaining) by apply(adler_lane_iterator_index_bounds(total, remaining)) using { 0 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) <= 5551 by apply(adler_lane_iterator_index_before_next(total, remaining)) using { 0 <= remaining; 4 <= remaining; remaining <= total; total <= 22208; };
        have adler_lane_vectors_consumed(total, remaining) < 5552 by arithmetic() using { adler_lane_vectors_consumed(total, remaining) <= 5551; };
        apply(adler_lane_native_b_sum_fits(adler_lane_vectors_consumed(total, remaining), a, b, byte)) using {
            0 <= adler_lane_vectors_consumed(total, remaining); adler_lane_vectors_consumed(total, remaining) < 5552;
            0 <= to_integer(a); to_integer(a) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(total, remaining));
            0 <= to_integer(b); to_integer(b) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining));
            0 <= to_integer(byte); to_integer(byte) <= 255;
        }
    }
}
