// Arithmetic ceilings for the unchanged adler2 deferred-reduction loop.
// These prove bounds on proposed lane invariants and their next additions.
// Establishing and preserving those invariants over the actual iterators is
// a separate obligation; no computed checksum result is assumed here.

function adler_lane_triangle(n: Integer) -> Integer {
    truncating_quotient(n * (n + 1), 2)
}

function adler_lane_a_ceiling(n: Integer) -> Integer { 65520 + 255 * n }
function adler_lane_b_ceiling(n: Integer) -> Integer {
    65520 + 65520 * n + 255 * adler_lane_triangle(n)
}

theorem adler_lane_half_product_5551(n: Integer, divisor: Integer) {
    requires 0 <= n;
    requires n <= 5551;
    requires 2 <= divisor;
    requires divisor <= 2;
    requires divisor != 0;
    ensures truncating_quotient(n * (n + 1), divisor) <= 15409576 by {
        have 1 <= n + 1 by arithmetic() using { 0 <= n; };
        have n + 1 <= 5552 by arithmetic() using { n <= 5551; };
        have 0 <= n * (n + 1) by {
            arithmetic_certificate rules {
                premise 0: 0 <= n => 0 <= n;
                premise 1: n <= 5551 => n <= 5551;
                premise 2: 1 <= n + 1 => 1 <= n + 1;
                premise 3: n + 1 <= 5552 => n + 1 <= 5552;
                integer_product_bounds bounds [0, 1, 2, 3] => 0 <= n * (n + 1);
                conclusion 0;
            }
        }
        have n * (n + 1) <= 30819152 by {
            arithmetic_certificate rules {
                premise 0: 0 <= n => 0 <= n;
                premise 1: n <= 5551 => n <= 5551;
                premise 2: 1 <= n + 1 => 1 <= n + 1;
                premise 3: n + 1 <= 5552 => n + 1 <= 5552;
                integer_product_bounds bounds [0, 1, 2, 3] => n * (n + 1) <= 30819152;
                conclusion 0;
            }
        }
        arithmetic_certificate rules {
            premise 0: 0 <= n * (n + 1) => 0 <= n * (n + 1);
            premise 1: n * (n + 1) <= 30819152 => n * (n + 1) <= 30819152;
            premise 2: 2 <= divisor => 2 <= divisor;
            premise 3: divisor <= 2 => divisor <= 2;
            integer_division_bounds bounds [0, 1, 2, 3] => truncating_quotient(n * (n + 1), divisor) <= 15409576;
            conclusion 0;
        }
    }
}

theorem adler_lane_triangle_5551(n: Integer) {
    requires 0 <= n;
    requires n <= 5551;
    ensures adler_lane_triangle(n) <= 15409576 by {
        unfold(adler_lane_triangle(n));
        apply(adler_lane_half_product_5551(n, 2)) using {
            0 <= n; n <= 5551; 2 <= 2; 2 <= 2; 2 != 0;
        }
    }
}

theorem adler_lane_ceiling_5551(n: Integer) {
    requires 0 <= n;
    requires n <= 5551;
    ensures adler_lane_a_ceiling(n) <= 1481025 by {
        unfold(adler_lane_a_ceiling(n));
        arithmetic() using { n <= 5551; }
    }
    ensures adler_lane_b_ceiling(n) <= 4293208920 by {
        have adler_lane_triangle(n) <= 15409576 by apply(adler_lane_triangle_5551(n)) using { 0 <= n; n <= 5551; };
        unfold(adler_lane_b_ceiling(n));
        arithmetic() using { n <= 5551; adler_lane_triangle(n) <= 15409576; }
    }
}

theorem adler_lane_half_product_5552(n: Integer, divisor: Integer) {
    requires 0 <= n;
    requires n <= 5552;
    requires 2 <= divisor;
    requires divisor <= 2;
    requires divisor != 0;
    ensures truncating_quotient(n * (n + 1), divisor) <= 15415128 by {
        have 1 <= n + 1 by arithmetic() using { 0 <= n; };
        have n + 1 <= 5553 by arithmetic() using { n <= 5552; };
        have 0 <= n * (n + 1) by {
            arithmetic_certificate rules {
                premise 0: 0 <= n => 0 <= n;
                premise 1: n <= 5552 => n <= 5552;
                premise 2: 1 <= n + 1 => 1 <= n + 1;
                premise 3: n + 1 <= 5553 => n + 1 <= 5553;
                integer_product_bounds bounds [0, 1, 2, 3] => 0 <= n * (n + 1);
                conclusion 0;
            }
        }
        have n * (n + 1) <= 30830256 by {
            arithmetic_certificate rules {
                premise 0: 0 <= n => 0 <= n;
                premise 1: n <= 5552 => n <= 5552;
                premise 2: 1 <= n + 1 => 1 <= n + 1;
                premise 3: n + 1 <= 5553 => n + 1 <= 5553;
                integer_product_bounds bounds [0, 1, 2, 3] => n * (n + 1) <= 30830256;
                conclusion 0;
            }
        }
        arithmetic_certificate rules {
            premise 0: 0 <= n * (n + 1) => 0 <= n * (n + 1);
            premise 1: n * (n + 1) <= 30830256 => n * (n + 1) <= 30830256;
            premise 2: 2 <= divisor => 2 <= divisor;
            premise 3: divisor <= 2 => divisor <= 2;
            integer_division_bounds bounds [0, 1, 2, 3] => truncating_quotient(n * (n + 1), divisor) <= 15415128;
            conclusion 0;
        }
    }
}

theorem adler_lane_triangle_5552(n: Integer) {
    requires 0 <= n;
    requires n <= 5552;
    ensures adler_lane_triangle(n) <= 15415128 by {
        unfold(adler_lane_triangle(n));
        apply(adler_lane_half_product_5552(n, 2)) using {
            0 <= n; n <= 5552; 2 <= 2; 2 <= 2; 2 != 0;
        }
    }
}

theorem adler_lane_ceiling_5552(n: Integer) {
    requires 0 <= n;
    requires n <= 5552;
    ensures adler_lane_a_ceiling(n) <= 1481280 by {
        unfold(adler_lane_a_ceiling(n));
        arithmetic() using { n <= 5552; }
    }
    ensures adler_lane_b_ceiling(n) <= 4294690200 by {
        have adler_lane_triangle(n) <= 15415128 by apply(adler_lane_triangle_5552(n)) using { 0 <= n; n <= 5552; };
        unfold(adler_lane_b_ceiling(n));
        arithmetic() using { n <= 5552; adler_lane_triangle(n) <= 15415128; }
    }
}

theorem adler_lane_initial_ceiling() {
    ensures adler_lane_a_ceiling(0) == 65520 by {
        unfold(adler_lane_a_ceiling(0)); normalize();
    }
    ensures adler_lane_b_ceiling(0) == 65520 by {
        unfold(adler_lane_b_ceiling(0));
        unfold(adler_lane_triangle(0)); normalize();
    }
}

theorem adler_lane_step_a(n: Integer, a: Integer, byte: Integer) {
    requires 0 <= n;
    requires n < 5552;
    requires 0 <= a;
    requires a <= adler_lane_a_ceiling(n);
    requires 0 <= byte;
    requires byte <= 255;
    ensures 0 <= a + byte by arithmetic() using { 0 <= a; 0 <= byte; };
    ensures a + byte <= 1481280 by {
        have n <= 5551 by arithmetic() using { n < 5552; };
        have adler_lane_a_ceiling(n) <= 1481025 by apply(adler_lane_ceiling_5551(n)) using { 0 <= n; n <= 5551; };
        arithmetic_certificate {
            premise 0: a <= adler_lane_a_ceiling(n) => a <= adler_lane_a_ceiling(n);
            premise 1: adler_lane_a_ceiling(n) <= 1481025 => adler_lane_a_ceiling(n) <= 1481025;
            premise 2: byte <= 255 => byte <= 255;
            add 0, 1 => a <= 1481025;
            add 3, 2 => a + byte <= 1481280;
            conclusion 4;
        }
    }
}

theorem adler_lane_step_b(n: Integer, a: Integer, b: Integer, byte: Integer) {
    requires 0 <= n;
    requires n < 5552;
    requires 0 <= a;
    requires a <= adler_lane_a_ceiling(n);
    requires 0 <= b;
    requires b <= adler_lane_b_ceiling(n);
    requires 0 <= byte;
    requires byte <= 255;
    ensures 0 <= b + (a + byte) by { arithmetic_certificate {
        premise 0: 0 <= b => 0 <= b;
        premise 1: 0 <= a => 0 <= a;
        premise 2: 0 <= byte => 0 <= byte;
        add 0, 1 => 0 <= b + a;
        add 3, 2 => 0 <= b + (a + byte);
        conclusion 4;
    } }
    ensures b + (a + byte) <= 4294690200 by {
        have n <= 5551 by arithmetic() using { n < 5552; };
        have adler_lane_b_ceiling(n) <= 4293208920 by apply(adler_lane_ceiling_5551(n)) using { 0 <= n; n <= 5551; };
        have a + byte <= 1481280 by apply(adler_lane_step_a(n, a, byte)) using {
                0 <= n; n < 5552; 0 <= a; a <= adler_lane_a_ceiling(n); 0 <= byte; byte <= 255;
            };
        arithmetic_certificate {
            premise 0: b <= adler_lane_b_ceiling(n) => b <= adler_lane_b_ceiling(n);
            premise 1: adler_lane_b_ceiling(n) <= 4293208920 => adler_lane_b_ceiling(n) <= 4293208920;
            premise 2: a + byte <= 1481280 => a + byte <= 1481280;
            add 0, 1 => b <= 4293208920;
            add 3, 2 => b + (a + byte) <= 4294690200;
            conclusion 4;
        }
    }
}

theorem adler_lane_limit_is_tight() {
    ensures adler_lane_b_ceiling(5552) == 4294690200 by {
        unfold(adler_lane_b_ceiling(5552)); unfold(adler_lane_triangle(5552)); normalize();
    }
    ensures adler_lane_b_ceiling(5552) <= 4294967295 by {
        unfold(adler_lane_b_ceiling(5552)); unfold(adler_lane_triangle(5552)); normalize();
    }
    ensures adler_lane_b_ceiling(5553) == 4296171735 by {
        unfold(adler_lane_b_ceiling(5553)); unfold(adler_lane_triangle(5553)); normalize();
    }
    ensures adler_lane_b_ceiling(5553) > 4294967295 by {
        unfold(adler_lane_b_ceiling(5553)); unfold(adler_lane_triangle(5553)); normalize();
    }
}
theorem adler_lane_a_invariant_step(n: Integer, a: Integer, byte: Integer) {
    requires a <= adler_lane_a_ceiling(n);
    requires byte <= 255;
    ensures a + byte <= adler_lane_a_ceiling(n + 1) by {
        have adler_lane_a_ceiling(n) == 65520 + 255 * n by {
            unfold(adler_lane_a_ceiling(n)); normalize();
        }
        have a <= 65520 + 255 * n by arithmetic() using {
                a <= adler_lane_a_ceiling(n);
                adler_lane_a_ceiling(n) == 65520 + 255 * n;
            };
        unfold(adler_lane_a_ceiling(n + 1));
        arithmetic() using { a <= 65520 + 255 * n; byte <= 255; }
    }
}

theorem adler_lane_triangle_successor(n: Integer) {
    requires 0 <= n;
    requires n <= 5551;
    ensures adler_lane_triangle(n + 1) == adler_lane_triangle(n) + (n + 1) by {
        have 1 <= n + 1 by arithmetic() using { 0 <= n; };
        have n + 1 <= 5552 by arithmetic() using { n <= 5551; };
        have 0 <= n + 1 by arithmetic() using { 0 <= n; };
        have 0 <= n * (n + 1) by {
            arithmetic_certificate rules {
                premise 0: 0 <= n => 0 <= n;
                premise 1: n <= 5551 => n <= 5551;
                premise 2: 1 <= n + 1 => 1 <= n + 1;
                premise 3: n + 1 <= 5552 => n + 1 <= 5552;
                integer_product_bounds bounds [0, 1, 2, 3] => 0 <= n * (n + 1);
                conclusion 0;
            }
        }
        have (n + 1) * ((n + 1) + 1) == n * (n + 1) + 2 * (n + 1) by {
            arithmetic_certificate rules {
                integer_polynomial_identity bounds [] => (n + 1) * ((n + 1) + 1) == n * (n + 1) + 2 * (n + 1);
                conclusion 0;
            }
        }
        unfold(adler_lane_triangle(n + 1));
        unfold(adler_lane_triangle(n));
        rewrite((n + 1) * ((n + 1) + 1) == n * (n + 1) + 2 * (n + 1));
        arithmetic_certificate rules {
            premise 0: 0 <= n * (n + 1) => 0 <= n * (n + 1);
            premise 1: 0 <= n + 1 => 0 <= n + 1;
            integer_quotient_shift bounds [0, 1] => truncating_quotient(n * (n + 1) + 2 * (n + 1), 2) == truncating_quotient(n * (n + 1), 2) + (n + 1);
            conclusion 0;
        }
    }
}

theorem adler_lane_b_ceiling_successor(n: Integer) {
    requires 0 <= n;
    requires n <= 5551;
    ensures adler_lane_b_ceiling(n + 1) == adler_lane_b_ceiling(n) + adler_lane_a_ceiling(n + 1) by {
        have adler_lane_triangle(n + 1) == adler_lane_triangle(n) + (n + 1) by apply(adler_lane_triangle_successor(n)) using { 0 <= n; n <= 5551; };
        unfold(adler_lane_b_ceiling(n + 1));
        unfold(adler_lane_b_ceiling(n));
        unfold(adler_lane_a_ceiling(n + 1));
        rewrite(adler_lane_triangle(n + 1) == adler_lane_triangle(n) + (n + 1));
        arithmetic_certificate rules {
            integer_polynomial_identity bounds [] => 65520 + 65520 * (n + 1) + 255 * (adler_lane_triangle(n) + (n + 1)) == (65520 + 65520 * n + 255 * adler_lane_triangle(n)) + (65520 + 255 * (n + 1));
            conclusion 0;
        }
    }
}

theorem adler_lane_b_invariant_step(n: Integer, a: Integer, b: Integer, byte: Integer) {
    requires 0 <= n;
    requires n < 5552;
    requires a <= adler_lane_a_ceiling(n);
    requires b <= adler_lane_b_ceiling(n);
    requires byte <= 255;
    ensures b + (a + byte) <= adler_lane_b_ceiling(n + 1) by {
        have n <= 5551 by arithmetic() using { n < 5552; };
        have a + byte <= adler_lane_a_ceiling(n + 1) by apply(adler_lane_a_invariant_step(n, a, byte)) using {
                a <= adler_lane_a_ceiling(n); byte <= 255;
            };
        have adler_lane_b_ceiling(n + 1) == adler_lane_b_ceiling(n) + adler_lane_a_ceiling(n + 1) by apply(adler_lane_b_ceiling_successor(n)) using { 0 <= n; n <= 5551; };
        rewrite(adler_lane_b_ceiling(n + 1) == adler_lane_b_ceiling(n) + adler_lane_a_ceiling(n + 1));
        arithmetic() using {
            b <= adler_lane_b_ceiling(n);
            a + byte <= adler_lane_a_ceiling(n + 1);
        }
    }
}

// These implications now reach the actual widened guard in U32X4::add_assign.
theorem adler_lane_native_a_sum_fits(n: Integer, a: uint32, byte: uint32) {
    requires 0 <= n;
    requires n < 5552;
    requires 0 <= to_integer(a);
    requires to_integer(a) <= adler_lane_a_ceiling(n);
    requires 0 <= to_integer(byte);
    requires to_integer(byte) <= 255;
    ensures to_integer(a) + to_integer(byte) <= 4294967295 by {
        have to_integer(a) + to_integer(byte) <= 1481280 by apply(adler_lane_step_a(n, to_integer(a), to_integer(byte))) using {
                0 <= n; n < 5552; 0 <= to_integer(a);
                to_integer(a) <= adler_lane_a_ceiling(n);
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        arithmetic() using { to_integer(a) + to_integer(byte) <= 1481280; }
    }
}

theorem adler_lane_native_a_step(n: Integer, a: uint32, byte: uint32) {
    requires 0 <= n;
    requires n < 5552;
    requires 0 <= to_integer(a);
    requires to_integer(a) <= adler_lane_a_ceiling(n);
    requires 0 <= to_integer(byte);
    requires to_integer(byte) <= 255;
    ensures ((int64)a + (int64)byte) <= 4294967295i64 by {
        have to_integer(a) + to_integer(byte) <= 4294967295 by apply(adler_lane_native_a_sum_fits(n, a, byte)) using {
                0 <= n; n < 5552; 0 <= to_integer(a);
                to_integer(a) <= adler_lane_a_ceiling(n);
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        apply(uint32_widened_add_guard_by_integer_bound(a, byte)) using {
            to_integer(a) + to_integer(byte) <= 4294967295;
        }
    }
    ensures to_integer(a + byte) == to_integer(a) + to_integer(byte) by {
        have to_integer(a) + to_integer(byte) <= 4294967295 by apply(adler_lane_native_a_sum_fits(n, a, byte)) using {
                0 <= n; n < 5552; 0 <= to_integer(a);
                to_integer(a) <= adler_lane_a_ceiling(n);
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        apply(uint32_add_to_integer(a, byte)) using {
            to_integer(a) + to_integer(byte) <= 4294967295;
        }
    }
    ensures to_integer(a + byte) <= adler_lane_a_ceiling(n + 1) by {
        have to_integer(a) + to_integer(byte) <= 4294967295 by apply(adler_lane_native_a_sum_fits(n, a, byte)) using {
                0 <= n; n < 5552; 0 <= to_integer(a);
                to_integer(a) <= adler_lane_a_ceiling(n);
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        have to_integer(a + byte) == to_integer(a) + to_integer(byte) by apply(uint32_add_to_integer(a, byte)) using { to_integer(a) + to_integer(byte) <= 4294967295; };
        rewrite(to_integer(a + byte) == to_integer(a) + to_integer(byte));
        apply(adler_lane_a_invariant_step(n, to_integer(a), to_integer(byte))) using {
            to_integer(a) <= adler_lane_a_ceiling(n); to_integer(byte) <= 255;
        }
    }
}

theorem adler_lane_native_b_sum_fits(n: Integer, a: uint32, b: uint32, byte: uint32) {
    requires 0 <= n;
    requires n < 5552;
    requires 0 <= to_integer(a);
    requires to_integer(a) <= adler_lane_a_ceiling(n);
    requires 0 <= to_integer(b);
    requires to_integer(b) <= adler_lane_b_ceiling(n);
    requires 0 <= to_integer(byte);
    requires to_integer(byte) <= 255;
    ensures to_integer(b) + to_integer(a + byte) <= 4294967295 by {
        have to_integer(a + byte) == to_integer(a) + to_integer(byte) by apply(adler_lane_native_a_step(n, a, byte)) using {
                0 <= n; n < 5552; 0 <= to_integer(a);
                to_integer(a) <= adler_lane_a_ceiling(n);
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        have to_integer(b) + (to_integer(a) + to_integer(byte)) <= 4294690200 by apply(adler_lane_step_b(n, to_integer(a), to_integer(b), to_integer(byte))) using {
                0 <= n; n < 5552; 0 <= to_integer(a);
                to_integer(a) <= adler_lane_a_ceiling(n);
                0 <= to_integer(b); to_integer(b) <= adler_lane_b_ceiling(n);
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        arithmetic() using {
            to_integer(b) + (to_integer(a) + to_integer(byte)) <= 4294690200;
            to_integer(a + byte) == to_integer(a) + to_integer(byte);
        }
    }
}

theorem adler_lane_native_b_step(n: Integer, a: uint32, b: uint32, byte: uint32) {
    requires 0 <= n;
    requires n < 5552;
    requires 0 <= to_integer(a);
    requires to_integer(a) <= adler_lane_a_ceiling(n);
    requires 0 <= to_integer(b);
    requires to_integer(b) <= adler_lane_b_ceiling(n);
    requires 0 <= to_integer(byte);
    requires to_integer(byte) <= 255;
    ensures ((int64)b + (int64)(a + byte)) <= 4294967295i64 by {
        have to_integer(b) + to_integer(a + byte) <= 4294967295 by apply(adler_lane_native_b_sum_fits(n, a, b, byte)) using {
                0 <= n; n < 5552; 0 <= to_integer(a);
                to_integer(a) <= adler_lane_a_ceiling(n);
                0 <= to_integer(b); to_integer(b) <= adler_lane_b_ceiling(n);
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        apply(uint32_widened_add_guard_by_integer_bound(b, a + byte)) using {
            to_integer(b) + to_integer(a + byte) <= 4294967295;
        }
    }
    ensures to_integer(b + (a + byte)) == to_integer(b) + to_integer(a + byte) by {
        have to_integer(b) + to_integer(a + byte) <= 4294967295 by apply(adler_lane_native_b_sum_fits(n, a, b, byte)) using {
                0 <= n; n < 5552; 0 <= to_integer(a);
                to_integer(a) <= adler_lane_a_ceiling(n);
                0 <= to_integer(b); to_integer(b) <= adler_lane_b_ceiling(n);
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        apply(uint32_add_to_integer(b, a + byte)) using {
            to_integer(b) + to_integer(a + byte) <= 4294967295;
        }
    }
    ensures to_integer(b + (a + byte)) <= adler_lane_b_ceiling(n + 1) by {
        have to_integer(b) + to_integer(a + byte) <= 4294967295 by apply(adler_lane_native_b_sum_fits(n, a, b, byte)) using {
                0 <= n; n < 5552; 0 <= to_integer(a);
                to_integer(a) <= adler_lane_a_ceiling(n);
                0 <= to_integer(b); to_integer(b) <= adler_lane_b_ceiling(n);
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        have to_integer(b + (a + byte)) == to_integer(b) + to_integer(a + byte) by apply(uint32_add_to_integer(b, a + byte)) using {
                to_integer(b) + to_integer(a + byte) <= 4294967295;
            };
        have to_integer(a + byte) == to_integer(a) + to_integer(byte) by apply(adler_lane_native_a_step(n, a, byte)) using {
                0 <= n; n < 5552; 0 <= to_integer(a);
                to_integer(a) <= adler_lane_a_ceiling(n);
                0 <= to_integer(byte); to_integer(byte) <= 255;
            };
        rewrite(to_integer(b + (a + byte)) == to_integer(b) + to_integer(a + byte));
        rewrite(to_integer(a + byte) == to_integer(a) + to_integer(byte));
        apply(adler_lane_b_invariant_step(n, to_integer(a), to_integer(b), to_integer(byte))) using {
            0 <= n; n < 5552; to_integer(a) <= adler_lane_a_ceiling(n);
            to_integer(b) <= adler_lane_b_ceiling(n); to_integer(byte) <= 255;
        }
    }
}
