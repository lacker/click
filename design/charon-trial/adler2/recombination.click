// Bounds for the original Adler32::compute lane recombination expressions.
// These conditional arithmetic lemmas do not establish the loop invariants.
// The unchanged Rust source and Charon import are not modified.

theorem adler_recombine_difference(a: uint32) {
    requires a < 65521u32;
    ensures to_integer(65521u32 - a) == 65521 - to_integer(a)
        and 0 <= to_integer(65521u32 - a)
        and to_integer(65521u32 - a) <= 65521
        and 65521u32 - a <= 65521u32 by {
        have a <= 65521u32 by arithmetic() using { a < 65521u32; };
        apply(uint32_subtract_to_integer(65521u32, a)) using { a <= 65521u32; }
        apply(uint32_to_integer_bounds(a));
        apply(uint32_less_equal_to_integer(a, 65521u32)) using { a <= 65521u32; }
        have to_integer(65521u32 - a) == 65521 - to_integer(a) by simp() using { to_integer(65521u32 - a) == to_integer(65521u32) - to_integer(a); };
        have 0 <= to_integer(65521u32 - a) by {
            rewrite(to_integer(65521u32 - a) == 65521 - to_integer(a));
            arithmetic() using { to_integer(a) <= 65521; }
        }
        have to_integer(65521u32 - a) <= 65521 by {
            rewrite(to_integer(65521u32 - a) == 65521 - to_integer(a));
            arithmetic() using { 0 <= to_integer(a); }
        }
        apply(uint32_to_integer_less_equal_implies_less_equal(65521u32 - a, 65521u32)) using { to_integer(65521u32 - a) <= 65521; }
        assumption();
    }
}

theorem adler_recombine_lane_1(a: uint32, b: uint32) {
    requires a < 65521u32;
    requires to_integer(b) <= 262080;
    ensures to_integer(b + (65521u32 - a)) == to_integer(b) + (65521 - to_integer(a)) * 1
        and to_integer(b + (65521u32 - a)) <= 327601
        and ((int64)b + (int64)(65521u32 - a)) <= 4294967295i64 by {
        apply(adler_recombine_difference(a)) using { a < 65521u32; }
        have to_integer(b) + to_integer(65521u32 - a) <= 4294967295 by arithmetic() using { to_integer(b) <= 262080; to_integer(65521u32 - a) <= 65521; };
        apply(uint32_widened_add_guard_by_integer_bound(b, 65521u32 - a)) using { to_integer(b) + to_integer(65521u32 - a) <= 4294967295; }
        apply(uint32_add_to_integer(b, 65521u32 - a)) using { to_integer(b) + to_integer(65521u32 - a) <= 4294967295; }
        have to_integer(b + (65521u32 - a)) <= 327601 by { rewrite(to_integer(b + (65521u32 - a)) == to_integer(b) + to_integer(65521u32 - a)); arithmetic() using { to_integer(b) <= 262080; to_integer(65521u32 - a) <= 65521; } }
        have to_integer(b + (65521u32 - a)) == to_integer(b) + (65521 - to_integer(a)) * 1 by {
            rewrite(to_integer(b + (65521u32 - a)) == to_integer(b) + to_integer(65521u32 - a));
            rewrite(to_integer(65521u32 - a) == 65521 - to_integer(a)); simp() using {};
        }
        assumption();
    }
}

theorem adler_recombine_lane_2(a: uint32, b: uint32) {
    requires a < 65521u32;
    requires to_integer(b) <= 262080;
    ensures to_integer(b + ((65521u32 - a) * 2u32)) == to_integer(b) + (65521 - to_integer(a)) * 2
        and to_integer(b + ((65521u32 - a) * 2u32)) <= 393122
        and ((int64)b + (int64)((65521u32 - a) * 2u32)) <= 4294967295i64 by {
        apply(adler_recombine_difference(a)) using { a < 65521u32; }
        have 65521u32 - a <= 4294967295u32 / 2u32 by arithmetic() using { 65521u32 - a <= 65521u32; };
        have 2u32 == 0u32 or 65521u32 - a <= 4294967295u32 / 2u32 by assumption();
        apply(uint32_multiply_to_integer(65521u32 - a, 2u32)) using { 2u32 == 0u32 or 65521u32 - a <= 4294967295u32 / 2u32; }
        have to_integer((65521u32 - a) * 2u32) == (65521 - to_integer(a)) * 2 by {
            rewrite(to_integer((65521u32 - a) * 2u32) == to_integer(65521u32 - a) * to_integer(2u32));
            rewrite(to_integer(65521u32 - a) == 65521 - to_integer(a)); simp() using {};
        }
        have to_integer((65521u32 - a) * 2u32) <= 131042 by { rewrite(to_integer((65521u32 - a) * 2u32) == to_integer(65521u32 - a) * 2); arithmetic() using { to_integer(65521u32 - a) <= 65521; } }
        have to_integer(b) + to_integer((65521u32 - a) * 2u32) <= 4294967295 by arithmetic() using { to_integer(b) <= 262080; to_integer((65521u32 - a) * 2u32) <= 131042; };
        apply(uint32_widened_add_guard_by_integer_bound(b, (65521u32 - a) * 2u32)) using { to_integer(b) + to_integer((65521u32 - a) * 2u32) <= 4294967295; }
        apply(uint32_add_to_integer(b, (65521u32 - a) * 2u32)) using { to_integer(b) + to_integer((65521u32 - a) * 2u32) <= 4294967295; }
        have to_integer(b + ((65521u32 - a) * 2u32)) <= 393122 by { rewrite(to_integer(b + ((65521u32 - a) * 2u32)) == to_integer(b) + to_integer((65521u32 - a) * 2u32)); arithmetic() using { to_integer(b) <= 262080; to_integer((65521u32 - a) * 2u32) <= 131042; } }
        have to_integer(b + ((65521u32 - a) * 2u32)) == to_integer(b) + (65521 - to_integer(a)) * 2 by {
            rewrite(to_integer(b + ((65521u32 - a) * 2u32)) == to_integer(b) + to_integer((65521u32 - a) * 2u32));
            rewrite(to_integer((65521u32 - a) * 2u32) == (65521 - to_integer(a)) * 2); simp() using {};
        }
        assumption();
    }
}

theorem adler_recombine_lane_3(a: uint32, b: uint32) {
    requires a < 65521u32;
    requires to_integer(b) <= 262080;
    ensures to_integer(b + ((65521u32 - a) * 3u32)) == to_integer(b) + (65521 - to_integer(a)) * 3
        and to_integer(b + ((65521u32 - a) * 3u32)) <= 458643
        and ((int64)b + (int64)((65521u32 - a) * 3u32)) <= 4294967295i64 by {
        apply(adler_recombine_difference(a)) using { a < 65521u32; }
        have 65521u32 - a <= 4294967295u32 / 3u32 by arithmetic() using { 65521u32 - a <= 65521u32; };
        have 3u32 == 0u32 or 65521u32 - a <= 4294967295u32 / 3u32 by assumption();
        apply(uint32_multiply_to_integer(65521u32 - a, 3u32)) using { 3u32 == 0u32 or 65521u32 - a <= 4294967295u32 / 3u32; }
        have to_integer((65521u32 - a) * 3u32) == (65521 - to_integer(a)) * 3 by {
            rewrite(to_integer((65521u32 - a) * 3u32) == to_integer(65521u32 - a) * to_integer(3u32));
            rewrite(to_integer(65521u32 - a) == 65521 - to_integer(a)); simp() using {};
        }
        have to_integer((65521u32 - a) * 3u32) <= 196563 by { rewrite(to_integer((65521u32 - a) * 3u32) == to_integer(65521u32 - a) * 3); arithmetic() using { to_integer(65521u32 - a) <= 65521; } }
        have to_integer(b) + to_integer((65521u32 - a) * 3u32) <= 4294967295 by arithmetic() using { to_integer(b) <= 262080; to_integer((65521u32 - a) * 3u32) <= 196563; };
        apply(uint32_widened_add_guard_by_integer_bound(b, (65521u32 - a) * 3u32)) using { to_integer(b) + to_integer((65521u32 - a) * 3u32) <= 4294967295; }
        apply(uint32_add_to_integer(b, (65521u32 - a) * 3u32)) using { to_integer(b) + to_integer((65521u32 - a) * 3u32) <= 4294967295; }
        have to_integer(b + ((65521u32 - a) * 3u32)) <= 458643 by { rewrite(to_integer(b + ((65521u32 - a) * 3u32)) == to_integer(b) + to_integer((65521u32 - a) * 3u32)); arithmetic() using { to_integer(b) <= 262080; to_integer((65521u32 - a) * 3u32) <= 196563; } }
        have to_integer(b + ((65521u32 - a) * 3u32)) == to_integer(b) + (65521 - to_integer(a)) * 3 by {
            rewrite(to_integer(b + ((65521u32 - a) * 3u32)) == to_integer(b) + to_integer((65521u32 - a) * 3u32));
            rewrite(to_integer((65521u32 - a) * 3u32) == (65521 - to_integer(a)) * 3); simp() using {};
        }
        assumption();
    }
}
