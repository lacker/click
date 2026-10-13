// Native vector transitions against the common specification at an arbitrary prefix.
// Assemble after the common specification and lane-state.click.
// The scalar B representative accounts for the deferred chunk contribution.

// A is independent of the deferred scalar B contribution between full batches.
theorem adler_four_lane_a_prefix_step(bytes: uint8[], n: int32, a_seed: Integer, a: Integer, a0: Integer, a1: Integer, a2: Integer, a3: Integer) {
 requires 0 <= n;
 requires n <= 2147483643;
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= a;
 requires 0 <= a0;
 requires 0 <= a1;
 requires 0 <= a2;
 requires 0 <= a3;
 requires truncating_remainder(adler_lane_a(a, a0, a1, a2, a3), 65521) == adler_spec_a(bytes, n, a_seed);
 ensures truncating_remainder(adler_lane_a(a, a0 + to_integer((int32)bytes[n]), a1 + to_integer((int32)bytes[n + 1]), a2 + to_integer((int32)bytes[n + 2]), a3 + to_integer((int32)bytes[n + 3])), 65521) == adler_spec_a(bytes, n + 4, a_seed) by {
  have n <= 2147483646 by arithmetic() using { n <= 2147483643; };
  have n <= 2147483645 by arithmetic() using { n <= 2147483643; };
  have n <= 2147483644 by arithmetic() using { n <= 2147483643; };
  have 0 <= adler_lane_a(a, a0, a1, a2, a3) by {
   unfold(adler_lane_a(a, a0, a1, a2, a3));
   arithmetic_certificate {
    premise 0: 0 <= a => 0 <= a;
    premise 1: 0 <= a0 => 0 <= a0;
    premise 2: 0 <= a1 => 0 <= a1;
    premise 3: 0 <= a2 => 0 <= a2;
    premise 4: 0 <= a3 => 0 <= a3;
    add 0, 1 => 0 <= a + a0;
    add 5, 2 => 0 <= a + a0 + a1;
    add 6, 3 => 0 <= a + a0 + a1 + a2;
    add 7, 4 => 0 <= a + a0 + a1 + a2 + a3;
    conclusion 8;
   }
  }
  apply(adler_four_lane_state_step(a, 0, a0, a1, a2, a3, 0, 0, 0, 0, to_integer((int32)bytes[n]), to_integer((int32)bytes[n + 1]), to_integer((int32)bytes[n + 2]), to_integer((int32)bytes[n + 3]))) using { 0 <= n; n <= 2147483646; n <= 2147483645; n <= 2147483644; };
  apply(adler_prefix_a_step_four(bytes, n, a_seed, adler_lane_a(a, a0, a1, a2, a3)));
  rewrite(adler_lane_a(a, a0 + to_integer((int32)bytes[n]), a1 + to_integer((int32)bytes[n + 1]), a2 + to_integer((int32)bytes[n + 2]), a3 + to_integer((int32)bytes[n + 3])) == adler_lane_a(a, a0, a1, a2, a3) + to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]));
  have adler_lane_a(a, a0, a1, a2, a3) + to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]) == adler_lane_a(a, a0, a1, a2, a3) + (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])) by arithmetic() using {};
  rewrite(adler_lane_a(a, a0, a1, a2, a3) + to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]) == adler_lane_a(a, a0, a1, a2, a3) + (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])));
  assumption();
 }
}

theorem adler_native_four_lane_a_prefix_step(bytes: uint8[], n: int32, a_seed: Integer, a: Integer, a0: uint32, a1: uint32, a2: uint32, a3: uint32, v0: uint32, v1: uint32, v2: uint32, v3: uint32) {
 requires 0 <= n;
 requires n <= 2147483643;
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= a;
 requires truncating_remainder(adler_lane_a(a, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes, n, a_seed);
 requires to_integer(v0) == to_integer((int32)bytes[n]);
 requires to_integer(a0) + to_integer(v0) <= 4294967295;
 requires to_integer(v1) == to_integer((int32)bytes[n + 1]);
 requires to_integer(a1) + to_integer(v1) <= 4294967295;
 requires to_integer(v2) == to_integer((int32)bytes[n + 2]);
 requires to_integer(a2) + to_integer(v2) <= 4294967295;
 requires to_integer(v3) == to_integer((int32)bytes[n + 3]);
 requires to_integer(a3) + to_integer(v3) <= 4294967295;
 ensures truncating_remainder(adler_lane_a(a, to_integer((a0 + v0)), to_integer((a1 + v1)), to_integer((a2 + v2)), to_integer((a3 + v3))), 65521) == adler_spec_a(bytes, n + 4, a_seed) by {
  apply(uint32_to_integer_bounds(a0));
  apply(uint32_add_to_integer(a0, v0));
  apply(uint32_to_integer_bounds(a1));
  apply(uint32_add_to_integer(a1, v1));
  apply(uint32_to_integer_bounds(a2));
  apply(uint32_add_to_integer(a2, v2));
  apply(uint32_to_integer_bounds(a3));
  apply(uint32_add_to_integer(a3, v3));
  apply(adler_four_lane_a_prefix_step(bytes, n, a_seed, a, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)));
  rewrite(to_integer(a0 + v0) == to_integer(a0) + to_integer(v0));
  rewrite(to_integer(a1 + v1) == to_integer(a1) + to_integer(v1));
  rewrite(to_integer(a2 + v2) == to_integer(a2) + to_integer(v2));
  rewrite(to_integer(a3 + v3) == to_integer(a3) + to_integer(v3));
  rewrite(to_integer(v0) == to_integer((int32)bytes[n]));
  rewrite(to_integer(v1) == to_integer((int32)bytes[n + 1]));
  rewrite(to_integer(v2) == to_integer((int32)bytes[n + 2]));
  rewrite(to_integer(v3) == to_integer((int32)bytes[n + 3]));
  assumption();
 }
}

theorem adler_four_lane_prefix_step(bytes: uint8[], n: int32, a_seed: Integer, b_seed: Integer, a: Integer, b: Integer, a0: Integer, a1: Integer, a2: Integer, a3: Integer, b0: Integer, b1: Integer, b2: Integer, b3: Integer) {
 requires 0 <= n;
 requires n <= 2147483643;
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= b_seed;
 requires 0 <= a;
 requires 0 <= a0;
 requires 0 <= a1;
 requires 0 <= a2;
 requires 0 <= a3;
 requires 0 <= adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3);
 requires truncating_remainder(adler_lane_a(a, a0, a1, a2, a3), 65521) == adler_spec_a(bytes, n, a_seed);
 requires truncating_remainder(adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3), 65521) == adler_spec_b(bytes, n, a_seed, b_seed);
 ensures truncating_remainder(adler_lane_a(a, a0 + to_integer((int32)bytes[n]), a1 + to_integer((int32)bytes[n + 1]), a2 + to_integer((int32)bytes[n + 2]), a3 + to_integer((int32)bytes[n + 3])), 65521) == adler_spec_a(bytes, n + 4, a_seed) by {
  apply(adler_four_lane_a_prefix_step(bytes, n, a_seed, a, a0, a1, a2, a3));
  assumption();
 }
 ensures truncating_remainder(adler_lane_b(b + 4 * a, a1 + to_integer((int32)bytes[n + 1]), a2 + to_integer((int32)bytes[n + 2]), a3 + to_integer((int32)bytes[n + 3]), b0 + a0 + to_integer((int32)bytes[n]), b1 + a1 + to_integer((int32)bytes[n + 1]), b2 + a2 + to_integer((int32)bytes[n + 2]), b3 + a3 + to_integer((int32)bytes[n + 3])), 65521) == adler_spec_b(bytes, n + 4, a_seed, b_seed) by {
  have n <= 2147483646 by arithmetic() using { n <= 2147483643; };
  have n <= 2147483645 by arithmetic() using { n <= 2147483643; };
  have n <= 2147483644 by arithmetic() using { n <= 2147483643; };
  have 0 <= adler_lane_a(a, a0, a1, a2, a3) by {
   unfold(adler_lane_a(a, a0, a1, a2, a3));
   arithmetic_certificate {
    premise 0: 0 <= a => 0 <= a;
    premise 1: 0 <= a0 => 0 <= a0;
    premise 2: 0 <= a1 => 0 <= a1;
    premise 3: 0 <= a2 => 0 <= a2;
    premise 4: 0 <= a3 => 0 <= a3;
    add 0, 1 => 0 <= a + a0;
    add 5, 2 => 0 <= a + a0 + a1;
    add 6, 3 => 0 <= a + a0 + a1 + a2;
    add 7, 4 => 0 <= a + a0 + a1 + a2 + a3;
    conclusion 8;
   }
  }
  apply(adler_four_lane_state_step(a, b, a0, a1, a2, a3, b0, b1, b2, b3, to_integer((int32)bytes[n]), to_integer((int32)bytes[n + 1]), to_integer((int32)bytes[n + 2]), to_integer((int32)bytes[n + 3]))) using { 0 <= n; n <= 2147483646; n <= 2147483645; n <= 2147483644; };
  apply(adler_prefix_b_step_four(bytes, n, a_seed, b_seed, adler_lane_a(a, a0, a1, a2, a3), adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3)));
  rewrite(adler_lane_b(b + 4 * a, a1 + to_integer((int32)bytes[n + 1]), a2 + to_integer((int32)bytes[n + 2]), a3 + to_integer((int32)bytes[n + 3]), b0 + a0 + to_integer((int32)bytes[n]), b1 + a1 + to_integer((int32)bytes[n + 1]), b2 + a2 + to_integer((int32)bytes[n + 2]), b3 + a3 + to_integer((int32)bytes[n + 3])) == adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3) + 4 * adler_lane_a(a, a0, a1, a2, a3) + 4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]));
  have adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3) + 4 * adler_lane_a(a, a0, a1, a2, a3) + 4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]) == adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3) + 4 * adler_lane_a(a, a0, a1, a2, a3) + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])) by arithmetic() using {};
  rewrite(adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3) + 4 * adler_lane_a(a, a0, a1, a2, a3) + 4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]) == adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3) + 4 * adler_lane_a(a, a0, a1, a2, a3) + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])));
  assumption();
 }
}

theorem adler_native_four_lane_prefix_step(bytes: uint8[], n: int32, a_seed: Integer, b_seed: Integer, a: Integer, b: Integer, a0: uint32, a1: uint32, a2: uint32, a3: uint32, b0: uint32, b1: uint32, b2: uint32, b3: uint32, v0: uint32, v1: uint32, v2: uint32, v3: uint32) {
 requires 0 <= n;
 requires n <= 2147483643;
 requires defined(n + 1);
 requires defined(n + 2);
 requires defined(n + 3);
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= b_seed;
 requires 0 <= a;
 requires 0 <= adler_lane_b(b, to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3));
 requires truncating_remainder(adler_lane_a(a, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes, n, a_seed);
 requires truncating_remainder(adler_lane_b(b, to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)), 65521) == adler_spec_b(bytes, n, a_seed, b_seed);
 requires to_integer(v0) == to_integer((int32)bytes[n]);
 requires to_integer(a0) + to_integer(v0) <= 4294967295;
 requires to_integer(b0) + (to_integer(a0) + to_integer(v0)) <= 4294967295;
 requires to_integer(v1) == to_integer((int32)bytes[n + 1]);
 requires to_integer(a1) + to_integer(v1) <= 4294967295;
 requires to_integer(b1) + (to_integer(a1) + to_integer(v1)) <= 4294967295;
 requires to_integer(v2) == to_integer((int32)bytes[n + 2]);
 requires to_integer(a2) + to_integer(v2) <= 4294967295;
 requires to_integer(b2) + (to_integer(a2) + to_integer(v2)) <= 4294967295;
 requires to_integer(v3) == to_integer((int32)bytes[n + 3]);
 requires to_integer(a3) + to_integer(v3) <= 4294967295;
 requires to_integer(b3) + (to_integer(a3) + to_integer(v3)) <= 4294967295;
 ensures truncating_remainder(adler_lane_a(a, to_integer((a0 + v0)), to_integer((a1 + v1)), to_integer((a2 + v2)), to_integer((a3 + v3))), 65521) == adler_spec_a(bytes, n + 4, a_seed) by {
  apply(adler_native_four_lane_a_prefix_step(bytes, n, a_seed, a, a0, a1, a2, a3, v0, v1, v2, v3));
  assumption();
 }
 ensures truncating_remainder(adler_lane_b(b + 4 * a, to_integer((a1 + v1)), to_integer((a2 + v2)), to_integer((a3 + v3)), to_integer((b0 + (a0 + v0))), to_integer((b1 + (a1 + v1))), to_integer((b2 + (a2 + v2))), to_integer((b3 + (a3 + v3)))), 65521) == adler_spec_b(bytes, n + 4, a_seed, b_seed) by {
  have n <= 2147483646 by arithmetic() using { n <= 2147483643; };
  have n <= 2147483645 by arithmetic() using { n <= 2147483643; };
  have n <= 2147483644 by arithmetic() using { n <= 2147483643; };
  apply(uint32_to_integer_bounds(a0));
  apply(uint32_add_to_integer(a0, v0));
  have to_integer(b0) + to_integer(a0 + v0) <= 4294967295 by { rewrite(to_integer(a0 + v0) == to_integer(a0) + to_integer(v0)); assumption(); }
  apply(uint32_add_to_integer(b0, a0 + v0));
  apply(uint32_to_integer_bounds(a1));
  apply(uint32_add_to_integer(a1, v1));
  have to_integer(b1) + to_integer(a1 + v1) <= 4294967295 by { rewrite(to_integer(a1 + v1) == to_integer(a1) + to_integer(v1)); assumption(); }
  apply(uint32_add_to_integer(b1, a1 + v1));
  apply(uint32_to_integer_bounds(a2));
  apply(uint32_add_to_integer(a2, v2));
  have to_integer(b2) + to_integer(a2 + v2) <= 4294967295 by { rewrite(to_integer(a2 + v2) == to_integer(a2) + to_integer(v2)); assumption(); }
  apply(uint32_add_to_integer(b2, a2 + v2));
  apply(uint32_to_integer_bounds(a3));
  apply(uint32_add_to_integer(a3, v3));
  have to_integer(b3) + to_integer(a3 + v3) <= 4294967295 by { rewrite(to_integer(a3 + v3) == to_integer(a3) + to_integer(v3)); assumption(); }
  apply(uint32_add_to_integer(b3, a3 + v3));
  apply(adler_four_lane_prefix_step(bytes, n, a_seed, b_seed, a, b, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)));
  rewrite(to_integer(b0 + (a0 + v0)) == to_integer(b0) + to_integer(a0 + v0));
  rewrite(to_integer(b1 + (a1 + v1)) == to_integer(b1) + to_integer(a1 + v1));
  rewrite(to_integer(b2 + (a2 + v2)) == to_integer(b2) + to_integer(a2 + v2));
  rewrite(to_integer(b3 + (a3 + v3)) == to_integer(b3) + to_integer(a3 + v3));
  rewrite(to_integer(a0 + v0) == to_integer(a0) + to_integer(v0));
  rewrite(to_integer(a1 + v1) == to_integer(a1) + to_integer(v1));
  rewrite(to_integer(a2 + v2) == to_integer(a2) + to_integer(v2));
  rewrite(to_integer(a3 + v3) == to_integer(a3) + to_integer(v3));
  rewrite(to_integer(v0) == to_integer((int32)bytes[n]));
  rewrite(to_integer(v1) == to_integer((int32)bytes[n + 1]));
  rewrite(to_integer(v2) == to_integer((int32)bytes[n + 2]));
  rewrite(to_integer(v3) == to_integer((int32)bytes[n + 3]));
  have to_integer(b0) + (to_integer(a0) + to_integer((int32)bytes[n])) == to_integer(b0) + to_integer(a0) + to_integer((int32)bytes[n]) by arithmetic() using {};
  rewrite(to_integer(b0) + (to_integer(a0) + to_integer((int32)bytes[n])) == to_integer(b0) + to_integer(a0) + to_integer((int32)bytes[n]));
  have to_integer(b1) + (to_integer(a1) + to_integer((int32)bytes[n + 1])) == to_integer(b1) + to_integer(a1) + to_integer((int32)bytes[n + 1]) by arithmetic() using {};
  rewrite(to_integer(b1) + (to_integer(a1) + to_integer((int32)bytes[n + 1])) == to_integer(b1) + to_integer(a1) + to_integer((int32)bytes[n + 1]));
  have to_integer(b2) + (to_integer(a2) + to_integer((int32)bytes[n + 2])) == to_integer(b2) + to_integer(a2) + to_integer((int32)bytes[n + 2]) by arithmetic() using {};
  rewrite(to_integer(b2) + (to_integer(a2) + to_integer((int32)bytes[n + 2])) == to_integer(b2) + to_integer(a2) + to_integer((int32)bytes[n + 2]));
  have to_integer(b3) + (to_integer(a3) + to_integer((int32)bytes[n + 3])) == to_integer(b3) + to_integer(a3) + to_integer((int32)bytes[n + 3]) by arithmetic() using {};
  rewrite(to_integer(b3) + (to_integer(a3) + to_integer((int32)bytes[n + 3])) == to_integer(b3) + to_integer(a3) + to_integer((int32)bytes[n + 3]));
  assumption();
 }
}

// A prefix derived from the stored signed iterator state; no generated count.
theorem adler_native_iterator_prefix_step(bytes: uint8[], total: int32, remaining: int32, a_seed: Integer, b_seed: Integer, a: Integer, b: Integer, a0: uint32, a1: uint32, a2: uint32, a3: uint32, b0: uint32, b1: uint32, b2: uint32, b3: uint32, v0: uint32, v1: uint32, v2: uint32, v3: uint32) {
 requires 0 <= total;
 requires total <= 22208;
 requires 4 <= remaining;
 requires remaining <= total;
 requires defined(total - remaining);
 requires defined((total - remaining) + 1);
 requires defined((total - remaining) + 2);
 requires defined((total - remaining) + 3);
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= b_seed;
 requires 0 <= a;
 requires 0 <= adler_lane_b(b, to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3));
 requires truncating_remainder(adler_lane_a(a, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes, (total - remaining), a_seed);
 requires truncating_remainder(adler_lane_b(b, to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)), 65521) == adler_spec_b(bytes, (total - remaining), a_seed, b_seed);
 requires to_integer(v0) == to_integer((int32)bytes[(total - remaining)]);
 requires to_integer(a0) + to_integer(v0) <= 4294967295;
 requires to_integer(b0) + (to_integer(a0) + to_integer(v0)) <= 4294967295;
 requires to_integer(v1) == to_integer((int32)bytes[(total - remaining) + 1]);
 requires to_integer(a1) + to_integer(v1) <= 4294967295;
 requires to_integer(b1) + (to_integer(a1) + to_integer(v1)) <= 4294967295;
 requires to_integer(v2) == to_integer((int32)bytes[(total - remaining) + 2]);
 requires to_integer(a2) + to_integer(v2) <= 4294967295;
 requires to_integer(b2) + (to_integer(a2) + to_integer(v2)) <= 4294967295;
 requires to_integer(v3) == to_integer((int32)bytes[(total - remaining) + 3]);
 requires to_integer(a3) + to_integer(v3) <= 4294967295;
 requires to_integer(b3) + (to_integer(a3) + to_integer(v3)) <= 4294967295;
 ensures truncating_remainder(adler_lane_a(a, to_integer((a0 + v0)), to_integer((a1 + v1)), to_integer((a2 + v2)), to_integer((a3 + v3))), 65521) == adler_spec_a(bytes, total - (remaining - 4), a_seed) by {
  have 0 <= total - remaining by arithmetic() using { 0 <= total; total <= 22208; 4 <= remaining; remaining <= total; };
  have total - remaining <= 2147483643 by arithmetic() using { 0 <= total; total <= 22208; 4 <= remaining; remaining <= total; };
  have total - (remaining - 4) == (total - remaining) + 4 by arithmetic() using { 0 <= total; total <= 22208; 4 <= remaining; remaining <= total; };
  apply(adler_native_four_lane_prefix_step(bytes, total - remaining, a_seed, b_seed, a, b, a0, a1, a2, a3, b0, b1, b2, b3, v0, v1, v2, v3)) using {
   0 <= total - remaining;
   total - remaining <= 2147483643;
   defined(total - remaining);
   defined((total - remaining) + 1);
   defined((total - remaining) + 2);
   defined((total - remaining) + 3);
   0 <= a_seed;
   a_seed <= 65520;
   0 <= b_seed;
   0 <= a;
   0 <= adler_lane_b(b, to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3));
   truncating_remainder(adler_lane_a(a, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes, (total - remaining), a_seed);
   truncating_remainder(adler_lane_b(b, to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)), 65521) == adler_spec_b(bytes, (total - remaining), a_seed, b_seed);
   to_integer(v0) == to_integer((int32)bytes[(total - remaining)]);
   to_integer(a0) + to_integer(v0) <= 4294967295;
   to_integer(b0) + (to_integer(a0) + to_integer(v0)) <= 4294967295;
   to_integer(v1) == to_integer((int32)bytes[(total - remaining) + 1]);
   to_integer(a1) + to_integer(v1) <= 4294967295;
   to_integer(b1) + (to_integer(a1) + to_integer(v1)) <= 4294967295;
   to_integer(v2) == to_integer((int32)bytes[(total - remaining) + 2]);
   to_integer(a2) + to_integer(v2) <= 4294967295;
   to_integer(b2) + (to_integer(a2) + to_integer(v2)) <= 4294967295;
   to_integer(v3) == to_integer((int32)bytes[(total - remaining) + 3]);
   to_integer(a3) + to_integer(v3) <= 4294967295;
   to_integer(b3) + (to_integer(a3) + to_integer(v3)) <= 4294967295;
  };
  rewrite(total - (remaining - 4) == (total - remaining) + 4);
  assumption();
 }
 ensures truncating_remainder(adler_lane_b(b + 4 * a, to_integer((a1 + v1)), to_integer((a2 + v2)), to_integer((a3 + v3)), to_integer((b0 + (a0 + v0))), to_integer((b1 + (a1 + v1))), to_integer((b2 + (a2 + v2))), to_integer((b3 + (a3 + v3)))), 65521) == adler_spec_b(bytes, total - (remaining - 4), a_seed, b_seed) by {
  have 0 <= total - remaining by arithmetic() using { 0 <= total; total <= 22208; 4 <= remaining; remaining <= total; };
  have total - remaining <= 2147483643 by arithmetic() using { 0 <= total; total <= 22208; 4 <= remaining; remaining <= total; };
  have total - (remaining - 4) == (total - remaining) + 4 by arithmetic() using { 0 <= total; total <= 22208; 4 <= remaining; remaining <= total; };
  apply(adler_native_four_lane_prefix_step(bytes, total - remaining, a_seed, b_seed, a, b, a0, a1, a2, a3, b0, b1, b2, b3, v0, v1, v2, v3)) using {
   0 <= total - remaining;
   total - remaining <= 2147483643;
   defined(total - remaining);
   defined((total - remaining) + 1);
   defined((total - remaining) + 2);
   defined((total - remaining) + 3);
   0 <= a_seed;
   a_seed <= 65520;
   0 <= b_seed;
   0 <= a;
   0 <= adler_lane_b(b, to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3));
   truncating_remainder(adler_lane_a(a, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes, (total - remaining), a_seed);
   truncating_remainder(adler_lane_b(b, to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)), 65521) == adler_spec_b(bytes, (total - remaining), a_seed, b_seed);
   to_integer(v0) == to_integer((int32)bytes[(total - remaining)]);
   to_integer(a0) + to_integer(v0) <= 4294967295;
   to_integer(b0) + (to_integer(a0) + to_integer(v0)) <= 4294967295;
   to_integer(v1) == to_integer((int32)bytes[(total - remaining) + 1]);
   to_integer(a1) + to_integer(v1) <= 4294967295;
   to_integer(b1) + (to_integer(a1) + to_integer(v1)) <= 4294967295;
   to_integer(v2) == to_integer((int32)bytes[(total - remaining) + 2]);
   to_integer(a2) + to_integer(v2) <= 4294967295;
   to_integer(b2) + (to_integer(a2) + to_integer(v2)) <= 4294967295;
   to_integer(v3) == to_integer((int32)bytes[(total - remaining) + 3]);
   to_integer(a3) + to_integer(v3) <= 4294967295;
   to_integer(b3) + (to_integer(a3) + to_integer(v3)) <= 4294967295;
  };
  rewrite(total - (remaining - 4) == (total - remaining) + 4);
  assumption();
 }
 ensures 0 <= remaining - 4 and remaining - 4 <= total by {
  have 0 <= remaining - 4 by arithmetic() using { 4 <= remaining; remaining <= total; total <= 22208; };
  have remaining - 4 <= total by arithmetic() using { 4 <= remaining; remaining <= total; total <= 22208; };
  simp();
 }

}
