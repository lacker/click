// Integer observations of the optimized four-lane state.
// Assemble after design/adler32-spec.click; every lemma is source-proved.
// These relations do not assume machine arithmetic is free of overflow.
// The computation must supply checked observations of its native operations.

function adler_lane_a(a: Integer, a0: Integer, a1: Integer, a2: Integer, a3: Integer) -> Integer {
 a + a0 + a1 + a2 + a3
}
// The original final recombination adds 6 * 65521 and subtracts
// lane weights 1, 2, 3. Keep this offset in the representative between
// batches; it vanishes after reduction. B representatives use Integer.
function adler_lane_b(b: Integer, a1: Integer, a2: Integer, a3: Integer, b0: Integer, b1: Integer, b2: Integer, b3: Integer) -> Integer {
 b + 4 * (b0 + b1 + b2 + b3) + 393126 - a1 - 2 * a2 - 3 * a3
}
theorem adler_four_lane_state_step(a: Integer, b: Integer, a0: Integer, a1: Integer, a2: Integer, a3: Integer, b0: Integer, b1: Integer, b2: Integer, b3: Integer, v0: Integer, v1: Integer, v2: Integer, v3: Integer) {
 ensures adler_lane_a(a, a0 + v0, a1 + v1, a2 + v2, a3 + v3) == adler_lane_a(a, a0, a1, a2, a3) + v0 + v1 + v2 + v3 by {
  unfold(adler_lane_a(a, a0 + v0, a1 + v1, a2 + v2, a3 + v3));
  unfold(adler_lane_a(a, a0, a1, a2, a3));
  arithmetic() using {};
 }
 ensures adler_lane_b(b + 4 * a, a1 + v1, a2 + v2, a3 + v3, b0 + a0 + v0, b1 + a1 + v1, b2 + a2 + v2, b3 + a3 + v3) == adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3) + 4 * adler_lane_a(a, a0, a1, a2, a3) + 4 * v0 + 3 * v1 + 2 * v2 + v3 by {
  unfold(adler_lane_b(b + 4 * a, a1 + v1, a2 + v2, a3 + v3, b0 + a0 + v0, b1 + a1 + v1, b2 + a2 + v2, b3 + a3 + v3));
  unfold(adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3));
  unfold(adler_lane_a(a, a0, a1, a2, a3));
  arithmetic() using {};
 }
}

theorem adler_lane_a_reduction(a: Integer, a0: Integer, a1: Integer, a2: Integer, a3: Integer) {
 requires 0 <= a;
 requires 0 <= a0;
 requires 0 <= a1;
 requires 0 <= a2;
 requires 0 <= a3;
 ensures truncating_remainder(adler_lane_a(a, a0, a1, a2, a3), 65521) == truncating_remainder(adler_lane_a(a, truncating_remainder(a0, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521)), 65521) by {
  apply(integer_truncation_identity(a0, 65521));
  apply(integer_nonnegative_dividend_remainder(a0, 65521));
  apply(integer_truncation_identity(a1, 65521));
  apply(integer_nonnegative_dividend_remainder(a1, 65521));
  apply(integer_truncation_identity(a2, 65521));
  apply(integer_nonnegative_dividend_remainder(a2, 65521));
  apply(integer_truncation_identity(a3, 65521));
  apply(integer_nonnegative_dividend_remainder(a3, 65521));
  have 0 <= adler_lane_a(a, a0, a1, a2, a3) by { unfold(adler_lane_a(a, a0, a1, a2, a3)); arithmetic_certificate { premise 0: 0 <= a => 0 <= a; premise 1: 0 <= a0 => 0 <= a0; premise 2: 0 <= a1 => 0 <= a1; premise 3: 0 <= a2 => 0 <= a2; premise 4: 0 <= a3 => 0 <= a3; add 0, 1 => 0 <= a + a0; add 5, 2 => 0 <= a + a0 + a1; add 6, 3 => 0 <= a + a0 + a1 + a2; add 7, 4 => 0 <= a + a0 + a1 + a2 + a3; conclusion 8; } }
  have 0 <= adler_lane_a(a, truncating_remainder(a0, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521)) by { unfold(adler_lane_a(a, truncating_remainder(a0, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521))); arithmetic_certificate { premise 0: 0 <= a => 0 <= a; premise 1: 0 <= truncating_remainder(a0, 65521) => 0 <= truncating_remainder(a0, 65521); premise 2: 0 <= truncating_remainder(a1, 65521) => 0 <= truncating_remainder(a1, 65521); premise 3: 0 <= truncating_remainder(a2, 65521) => 0 <= truncating_remainder(a2, 65521); premise 4: 0 <= truncating_remainder(a3, 65521) => 0 <= truncating_remainder(a3, 65521); add 0, 1 => 0 <= a + truncating_remainder(a0, 65521); add 5, 2 => 0 <= a + truncating_remainder(a0, 65521) + truncating_remainder(a1, 65521); add 6, 3 => 0 <= a + truncating_remainder(a0, 65521) + truncating_remainder(a1, 65521) + truncating_remainder(a2, 65521); add 7, 4 => 0 <= a + truncating_remainder(a0, 65521) + truncating_remainder(a1, 65521) + truncating_remainder(a2, 65521) + truncating_remainder(a3, 65521); conclusion 8; } }
  have adler_lane_a(a, a0, a1, a2, a3) == adler_lane_a(a, truncating_remainder(a0, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521)) + 65521 * (truncating_quotient(a0, 65521) + truncating_quotient(a1, 65521) + truncating_quotient(a2, 65521) + truncating_quotient(a3, 65521)) by { unfold(adler_lane_a(a, a0, a1, a2, a3)); unfold(adler_lane_a(a, truncating_remainder(a0, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521))); arithmetic() using { a0 == truncating_quotient(a0, 65521) * 65521 + truncating_remainder(a0, 65521); a1 == truncating_quotient(a1, 65521) * 65521 + truncating_remainder(a1, 65521); a2 == truncating_quotient(a2, 65521) * 65521 + truncating_remainder(a2, 65521); a3 == truncating_quotient(a3, 65521) * 65521 + truncating_remainder(a3, 65521); } }
  apply(adler_residue_congruent(adler_lane_a(a, a0, a1, a2, a3), adler_lane_a(a, truncating_remainder(a0, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521)), truncating_quotient(a0, 65521) + truncating_quotient(a1, 65521) + truncating_quotient(a2, 65521) + truncating_quotient(a3, 65521)));
  assumption();
 }
}

// Reducing A lanes can increase this representative. The congruence
// witness may therefore be negative, even though every lane is unsigned.
// The old representative must be nonnegative for truncating remainder.
theorem adler_lane_b_reduction(b: Integer, a1: Integer, a2: Integer, a3: Integer, b0: Integer, b1: Integer, b2: Integer, b3: Integer) {
 requires 0 <= b;
 requires 0 <= a1;
 requires 0 <= a2;
 requires 0 <= a3;
 requires 0 <= b0;
 requires 0 <= b1;
 requires 0 <= b2;
 requires 0 <= b3;
 requires 0 <= adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3);
 ensures truncating_remainder(adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3), 65521) == truncating_remainder(adler_lane_b(truncating_remainder(b, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521), truncating_remainder(b0, 65521), truncating_remainder(b1, 65521), truncating_remainder(b2, 65521), truncating_remainder(b3, 65521)), 65521) by {
  apply(integer_truncation_identity(b, 65521));
  apply(integer_nonnegative_dividend_remainder(b, 65521));
  apply(integer_truncation_identity(a1, 65521));
  apply(integer_nonnegative_dividend_remainder(a1, 65521));
  apply(integer_truncation_identity(a2, 65521));
  apply(integer_nonnegative_dividend_remainder(a2, 65521));
  apply(integer_truncation_identity(a3, 65521));
  apply(integer_nonnegative_dividend_remainder(a3, 65521));
  apply(integer_truncation_identity(b0, 65521));
  apply(integer_nonnegative_dividend_remainder(b0, 65521));
  apply(integer_truncation_identity(b1, 65521));
  apply(integer_nonnegative_dividend_remainder(b1, 65521));
  apply(integer_truncation_identity(b2, 65521));
  apply(integer_nonnegative_dividend_remainder(b2, 65521));
  apply(integer_truncation_identity(b3, 65521));
  apply(integer_nonnegative_dividend_remainder(b3, 65521));
  apply(integer_positive_divisor_remainder_upper(a1, 65521));
  apply(integer_positive_divisor_remainder_upper(a2, 65521));
  apply(integer_positive_divisor_remainder_upper(a3, 65521));
  have 0 <= truncating_remainder(b, 65521) + 4 * (truncating_remainder(b0, 65521) + truncating_remainder(b1, 65521) + truncating_remainder(b2, 65521) + truncating_remainder(b3, 65521)) by { arithmetic_certificate {
   premise 0: 0 <= truncating_remainder(b, 65521) => 0 <= truncating_remainder(b, 65521);
   premise 1: 0 <= truncating_remainder(b0, 65521) => 0 <= truncating_remainder(b0, 65521);
   premise 2: 0 <= truncating_remainder(b1, 65521) => 0 <= truncating_remainder(b1, 65521);
   premise 3: 0 <= truncating_remainder(b2, 65521) => 0 <= truncating_remainder(b2, 65521);
   premise 4: 0 <= truncating_remainder(b3, 65521) => 0 <= truncating_remainder(b3, 65521);
   scale 1 by 4 => 0 <= 4 * truncating_remainder(b0, 65521);
   scale 2 by 4 => 0 <= 4 * truncating_remainder(b1, 65521);
   scale 3 by 4 => 0 <= 4 * truncating_remainder(b2, 65521);
   scale 4 by 4 => 0 <= 4 * truncating_remainder(b3, 65521);
   add 0, 5 => 0 <= truncating_remainder(b, 65521) + 4 * truncating_remainder(b0, 65521);
   add 9, 6 => 0 <= truncating_remainder(b, 65521) + 4 * truncating_remainder(b0, 65521) + 4 * truncating_remainder(b1, 65521);
   add 10, 7 => 0 <= truncating_remainder(b, 65521) + 4 * truncating_remainder(b0, 65521) + 4 * truncating_remainder(b1, 65521) + 4 * truncating_remainder(b2, 65521);
   add 11, 8 => 0 <= truncating_remainder(b, 65521) + 4 * truncating_remainder(b0, 65521) + 4 * truncating_remainder(b1, 65521) + 4 * truncating_remainder(b2, 65521) + 4 * truncating_remainder(b3, 65521);
   conclusion 12;
  } }
  have truncating_remainder(a1, 65521) + 2 * truncating_remainder(a2, 65521) + 3 * truncating_remainder(a3, 65521) <= 393120 by { arithmetic_certificate {
   premise 0: truncating_remainder(a1, 65521) <= 65520 => truncating_remainder(a1, 65521) <= 65520;
   premise 1: truncating_remainder(a2, 65521) <= 65520 => truncating_remainder(a2, 65521) <= 65520;
   premise 2: truncating_remainder(a3, 65521) <= 65520 => truncating_remainder(a3, 65521) <= 65520;
   scale 1 by 2 => 2 * truncating_remainder(a2, 65521) <= 131040;
   scale 2 by 3 => 3 * truncating_remainder(a3, 65521) <= 196560;
   add 0, 3 => truncating_remainder(a1, 65521) + 2 * truncating_remainder(a2, 65521) <= 196560;
   add 5, 4 => truncating_remainder(a1, 65521) + 2 * truncating_remainder(a2, 65521) + 3 * truncating_remainder(a3, 65521) <= 393120;
   conclusion 6;
  } }
  have 0 <= adler_lane_b(truncating_remainder(b, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521), truncating_remainder(b0, 65521), truncating_remainder(b1, 65521), truncating_remainder(b2, 65521), truncating_remainder(b3, 65521)) by { unfold(adler_lane_b(truncating_remainder(b, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521), truncating_remainder(b0, 65521), truncating_remainder(b1, 65521), truncating_remainder(b2, 65521), truncating_remainder(b3, 65521))); arithmetic() using { 0 <= truncating_remainder(b, 65521) + 4 * (truncating_remainder(b0, 65521) + truncating_remainder(b1, 65521) + truncating_remainder(b2, 65521) + truncating_remainder(b3, 65521)); truncating_remainder(a1, 65521) + 2 * truncating_remainder(a2, 65521) + 3 * truncating_remainder(a3, 65521) <= 393120; } }
  have adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3) == adler_lane_b(truncating_remainder(b, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521), truncating_remainder(b0, 65521), truncating_remainder(b1, 65521), truncating_remainder(b2, 65521), truncating_remainder(b3, 65521)) + 65521 * (truncating_quotient(b, 65521) + 4 * (truncating_quotient(b0, 65521) + truncating_quotient(b1, 65521) + truncating_quotient(b2, 65521) + truncating_quotient(b3, 65521)) - truncating_quotient(a1, 65521) - 2 * truncating_quotient(a2, 65521) - 3 * truncating_quotient(a3, 65521)) by { unfold(adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3)); unfold(adler_lane_b(truncating_remainder(b, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521), truncating_remainder(b0, 65521), truncating_remainder(b1, 65521), truncating_remainder(b2, 65521), truncating_remainder(b3, 65521))); arithmetic() using { b == truncating_quotient(b, 65521) * 65521 + truncating_remainder(b, 65521); a1 == truncating_quotient(a1, 65521) * 65521 + truncating_remainder(a1, 65521); a2 == truncating_quotient(a2, 65521) * 65521 + truncating_remainder(a2, 65521); a3 == truncating_quotient(a3, 65521) * 65521 + truncating_remainder(a3, 65521); b0 == truncating_quotient(b0, 65521) * 65521 + truncating_remainder(b0, 65521); b1 == truncating_quotient(b1, 65521) * 65521 + truncating_remainder(b1, 65521); b2 == truncating_quotient(b2, 65521) * 65521 + truncating_remainder(b2, 65521); b3 == truncating_quotient(b3, 65521) * 65521 + truncating_remainder(b3, 65521); } }
  apply(adler_residue_congruent(adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3), adler_lane_b(truncating_remainder(b, 65521), truncating_remainder(a1, 65521), truncating_remainder(a2, 65521), truncating_remainder(a3, 65521), truncating_remainder(b0, 65521), truncating_remainder(b1, 65521), truncating_remainder(b2, 65521), truncating_remainder(b3, 65521)), truncating_quotient(b, 65521) + 4 * (truncating_quotient(b0, 65521) + truncating_quotient(b1, 65521) + truncating_quotient(b2, 65521) + truncating_quotient(b3, 65521)) - truncating_quotient(a1, 65521) - 2 * truncating_quotient(a2, 65521) - 3 * truncating_quotient(a3, 65521)));
  assumption();
 }
}

theorem adler_prefix_a_step_four(bytes: uint8[], n: int32, seed: Integer, representative: Integer) {
 requires 0 <= n;
 requires n <= 2147483643;
 requires 0 <= seed;
 requires 0 <= representative;
 requires truncating_remainder(representative, 65521) == adler_spec_a(bytes, n, seed);
 ensures truncating_remainder(representative + (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])), 65521) == adler_spec_a(bytes, n + 4, seed) by {
  have n <= 2147483646 by arithmetic() using { n <= 2147483643; };
  have n <= 2147483645 by arithmetic() using { n <= 2147483643; };
  have n <= 2147483644 by arithmetic() using { n <= 2147483643; };
  apply(adler_sum_nonnegative(bytes, n));
  have 0 <= (seed + adler_byte_sum(bytes, n)) by arithmetic() using { 0 <= seed; 0 <= adler_byte_sum(bytes, n); };
  apply(adler_byte_bounds(bytes[n]));
  apply(adler_byte_bounds(bytes[n + 1]));
  apply(adler_byte_bounds(bytes[n + 2]));
  apply(adler_byte_bounds(bytes[n + 3]));
  have 0 <= (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])) by { arithmetic_certificate {
   premise 0: 0 <= to_integer((int32)bytes[n]) => 0 <= to_integer((int32)bytes[n]);
   premise 1: 0 <= to_integer((int32)bytes[n + 1]) => 0 <= to_integer((int32)bytes[n + 1]);
   premise 2: 0 <= to_integer((int32)bytes[n + 2]) => 0 <= to_integer((int32)bytes[n + 2]);
   premise 3: 0 <= to_integer((int32)bytes[n + 3]) => 0 <= to_integer((int32)bytes[n + 3]);
   add 0, 1 => 0 <= to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]);
   add 4, 2 => 0 <= to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]);
   add 5, 3 => 0 <= (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]));
   conclusion 6;
  } }
  apply(adler_residue_add(representative, (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])))) using { n <= 2147483646; n <= 2147483645; n <= 2147483644; 0 <= representative; 0 <= (seed + adler_byte_sum(bytes, n)); 0 <= (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])); }
  apply(adler_residue_add((seed + adler_byte_sum(bytes, n)), (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])))) using { n <= 2147483646; n <= 2147483645; n <= 2147483644; 0 <= representative; 0 <= (seed + adler_byte_sum(bytes, n)); 0 <= (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])); }
  apply(adler_sum_append_four(bytes, n));
  have truncating_remainder(representative, 65521) == truncating_remainder((seed + adler_byte_sum(bytes, n)), 65521) by { rewrite(truncating_remainder(representative, 65521) == adler_spec_a(bytes, n, seed)); unfold(adler_spec_a(bytes, n, seed)); simp(); }
  have seed + adler_byte_sum(bytes, n + 4) == (seed + adler_byte_sum(bytes, n)) + (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])) by { rewrite(adler_byte_sum(bytes, n + 4) == adler_byte_sum(bytes, n) + to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])); arithmetic() using {}; }
  unfold(adler_spec_a(bytes, n + 4, seed));
  rewrite(seed + adler_byte_sum(bytes, n + 4) == (seed + adler_byte_sum(bytes, n)) + (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])));
  rewrite(truncating_remainder(representative + (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])), 65521) == truncating_remainder(truncating_remainder(representative, 65521) + truncating_remainder((to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])), 65521), 65521));
  rewrite(truncating_remainder((seed + adler_byte_sum(bytes, n)) + (to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])), 65521) == truncating_remainder(truncating_remainder((seed + adler_byte_sum(bytes, n)), 65521) + truncating_remainder((to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])), 65521), 65521));
  rewrite(truncating_remainder(representative, 65521) == truncating_remainder((seed + adler_byte_sum(bytes, n)), 65521));
  simp();
 }
}

theorem adler_prefix_a_step_one(bytes: uint8[], n: int32, seed: Integer, representative: Integer) {
 requires 0 <= n;
 requires n <= 2147483646;
 requires 0 <= seed;
 requires 0 <= representative;
 requires truncating_remainder(representative, 65521) == adler_spec_a(bytes, n, seed);
 ensures truncating_remainder(representative + to_integer((int32)bytes[n]), 65521) == adler_spec_a(bytes, n + 1, seed) by {
  apply(adler_sum_nonnegative(bytes, n));
  apply(adler_byte_bounds(bytes[n]));
  have 0 <= seed + adler_byte_sum(bytes, n) by arithmetic() using { 0 <= seed; 0 <= adler_byte_sum(bytes, n); };
  apply(adler_residue_add(representative, to_integer((int32)bytes[n])));
  apply(adler_residue_add(seed + adler_byte_sum(bytes, n), to_integer((int32)bytes[n])));
  have 0 < n + 1 by arithmetic() using { 0 <= n; n <= 2147483646; };
  apply(adler_sum_append(bytes, n + 1));
  have adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + to_integer((int32)bytes[n]) by { rewrite(adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n + 1 - 1) + to_integer((int32)bytes[n + 1 - 1])); normalize(); }
  have truncating_remainder(representative, 65521) == truncating_remainder(seed + adler_byte_sum(bytes, n), 65521) by { rewrite(truncating_remainder(representative, 65521) == adler_spec_a(bytes, n, seed)); unfold(adler_spec_a(bytes, n, seed)); simp(); }
  unfold(adler_spec_a(bytes, n + 1, seed));
  rewrite(adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + to_integer((int32)bytes[n]));
  have seed + (adler_byte_sum(bytes, n) + to_integer((int32)bytes[n])) == (seed + adler_byte_sum(bytes, n)) + to_integer((int32)bytes[n]) by arithmetic() using {};
  rewrite(seed + (adler_byte_sum(bytes, n) + to_integer((int32)bytes[n])) == (seed + adler_byte_sum(bytes, n)) + to_integer((int32)bytes[n]));
  rewrite(truncating_remainder(representative + to_integer((int32)bytes[n]), 65521) == truncating_remainder(truncating_remainder(representative, 65521) + truncating_remainder(to_integer((int32)bytes[n]), 65521), 65521));
  rewrite(truncating_remainder((seed + adler_byte_sum(bytes, n)) + to_integer((int32)bytes[n]), 65521) == truncating_remainder(truncating_remainder(seed + adler_byte_sum(bytes, n), 65521) + truncating_remainder(to_integer((int32)bytes[n]), 65521), 65521));
  rewrite(truncating_remainder(representative, 65521) == truncating_remainder(seed + adler_byte_sum(bytes, n), 65521));
  simp();
 }
}

theorem adler_prefix_b_step_four(bytes: uint8[], n: int32, a_seed: Integer, b_seed: Integer, a_rep: Integer, b_rep: Integer) {
 requires 0 <= n;
 requires n <= 2147483643;
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= b_seed;
 requires 0 <= a_rep;
 requires 0 <= b_rep;
 requires truncating_remainder(a_rep, 65521) == adler_spec_a(bytes, n, a_seed);
 requires truncating_remainder(b_rep, 65521) == adler_spec_b(bytes, n, a_seed, b_seed);
 ensures truncating_remainder((b_rep + 4 * a_rep + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]))), 65521) == adler_spec_b(bytes, n + 4, a_seed, b_seed) by {
  have n <= 2147483646 by arithmetic() using { n <= 2147483643; };
  have n <= 2147483645 by arithmetic() using { n <= 2147483643; };
  have n <= 2147483644 by arithmetic() using { n <= 2147483643; };
  apply(adler_sum_nonnegative(bytes, n));
  apply(adler_weighted_nonnegative(bytes, n));
  apply(adler_weighted_append_four(bytes, n));
  have defined(n + 4) by simp() using { 0 <= n; n <= 2147483643; };
  apply(int32_add_to_integer(n, 4)) using { defined(n + 4); };
  apply(int32_less_equal_to_integer(0, n));
  apply(int32_less_equal_to_integer(n, 2147483643));
  have 0 <= to_integer(n) * a_seed by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(n) => 0 <= to_integer(n);
   premise 1: to_integer(n) <= 2147483643 => to_integer(n) <= 2147483643;
   premise 2: 0 <= a_seed => 0 <= a_seed;
   premise 3: a_seed <= 65520 => a_seed <= 65520;
   integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(n) * a_seed; conclusion 0;
  } }
  have 0 <= (a_seed + adler_byte_sum(bytes, n)) by arithmetic() using { 0 <= a_seed; 0 <= adler_byte_sum(bytes, n); };
  have 0 <= b_seed + to_integer(n) * a_seed by arithmetic() using { 0 <= b_seed; 0 <= to_integer(n) * a_seed; };
  have 0 <= (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) by arithmetic() using { 0 <= b_seed + to_integer(n) * a_seed; 0 <= adler_weighted_sum(bytes, n, n); };
  apply(adler_byte_bounds(bytes[n]));
  apply(adler_byte_bounds(bytes[n + 1]));
  apply(adler_byte_bounds(bytes[n + 2]));
  apply(adler_byte_bounds(bytes[n + 3]));
  have 0 <= (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1])) by arithmetic() using { 0 <= to_integer((int32)bytes[n]); 0 <= to_integer((int32)bytes[n + 1]); };
  have 0 <= ((4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1])) + 2 * to_integer((int32)bytes[n + 2])) by arithmetic() using { 0 <= (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1])); 0 <= to_integer((int32)bytes[n + 2]); };
  have 0 <= (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])) by arithmetic() using { 0 <= ((4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1])) + 2 * to_integer((int32)bytes[n + 2])); 0 <= to_integer((int32)bytes[n + 3]); };
  have (to_integer(n) + to_integer(4)) * a_seed == to_integer(n) * a_seed + 4 * a_seed by { arithmetic_certificate rules { integer_polynomial_identity bounds [] => (to_integer(n) + to_integer(4)) * a_seed == to_integer(n) * a_seed + 4 * a_seed; conclusion 0; } }
  have (b_seed + to_integer(n + 4) * a_seed + adler_weighted_sum(bytes, n + 4, n + 4)) == (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) + 4 * (a_seed + adler_byte_sum(bytes, n)) + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])) by {
   rewrite(to_integer(n + 4) == to_integer(n) + to_integer(4));
   rewrite((to_integer(n) + to_integer(4)) * a_seed == to_integer(n) * a_seed + 4 * a_seed);
   rewrite(adler_weighted_sum(bytes, n + 4, n + 4) == adler_weighted_sum(bytes, n, n) + 4 * adler_byte_sum(bytes, n) + 4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])); arithmetic() using {};
  }
  have truncating_remainder(a_rep, 65521) == truncating_remainder((a_seed + adler_byte_sum(bytes, n)), 65521) by { rewrite(truncating_remainder(a_rep, 65521) == adler_spec_a(bytes, n, a_seed)); unfold(adler_spec_a(bytes, n, a_seed)); simp(); }
  have truncating_remainder(b_rep, 65521) == truncating_remainder((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521) by { rewrite(truncating_remainder(b_rep, 65521) == adler_spec_b(bytes, n, a_seed, b_seed)); unfold(adler_spec_b(bytes, n, a_seed, b_seed)); simp(); }
  apply(integer_truncation_identity(a_rep, 65521)) using { 65521 != 0; };
  apply(integer_truncation_identity(b_rep, 65521)) using { 65521 != 0; };
  apply(integer_truncation_identity((a_seed + adler_byte_sum(bytes, n)), 65521)) using { 65521 != 0; };
  apply(integer_truncation_identity((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521)) using { 65521 != 0; };
  have (b_rep + 4 * a_rep + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]))) == (b_seed + to_integer(n + 4) * a_seed + adler_weighted_sum(bytes, n + 4, n + 4)) + 65521 * (truncating_quotient(b_rep, 65521) - truncating_quotient((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521) + 4 * (truncating_quotient(a_rep, 65521) - truncating_quotient((a_seed + adler_byte_sum(bytes, n)), 65521))) by arithmetic() using { a_rep == truncating_quotient(a_rep, 65521) * 65521 + truncating_remainder(a_rep, 65521); b_rep == truncating_quotient(b_rep, 65521) * 65521 + truncating_remainder(b_rep, 65521); (a_seed + adler_byte_sum(bytes, n)) == truncating_quotient((a_seed + adler_byte_sum(bytes, n)), 65521) * 65521 + truncating_remainder((a_seed + adler_byte_sum(bytes, n)), 65521); (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) == truncating_quotient((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521) * 65521 + truncating_remainder((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521); truncating_remainder(a_rep, 65521) == truncating_remainder((a_seed + adler_byte_sum(bytes, n)), 65521); truncating_remainder(b_rep, 65521) == truncating_remainder((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521); (b_seed + to_integer(n + 4) * a_seed + adler_weighted_sum(bytes, n + 4, n + 4)) == (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) + 4 * (a_seed + adler_byte_sum(bytes, n)) + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])); };
  have 0 <= b_rep + 4 * a_rep by arithmetic() using { 0 <= b_rep; 0 <= a_rep; };
  have 0 <= (b_rep + 4 * a_rep + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]))) by arithmetic() using { 0 <= b_rep + 4 * a_rep; 0 <= (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])); };
  have 0 <= (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) + 4 * (a_seed + adler_byte_sum(bytes, n)) by arithmetic() using { 0 <= (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)); 0 <= (a_seed + adler_byte_sum(bytes, n)); };
  have 0 <= (b_seed + to_integer(n + 4) * a_seed + adler_weighted_sum(bytes, n + 4, n + 4)) by { rewrite((b_seed + to_integer(n + 4) * a_seed + adler_weighted_sum(bytes, n + 4, n + 4)) == (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) + 4 * (a_seed + adler_byte_sum(bytes, n)) + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]))); arithmetic() using { 0 <= (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) + 4 * (a_seed + adler_byte_sum(bytes, n)); 0 <= (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3])); } }
  apply(adler_residue_congruent((b_rep + 4 * a_rep + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]))), (b_seed + to_integer(n + 4) * a_seed + adler_weighted_sum(bytes, n + 4, n + 4)), (truncating_quotient(b_rep, 65521) - truncating_quotient((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521) + 4 * (truncating_quotient(a_rep, 65521) - truncating_quotient((a_seed + adler_byte_sum(bytes, n)), 65521))))) using { 0 <= n; n <= 2147483646; n <= 2147483645; n <= 2147483644; n <= 2147483643; 0 <= (b_rep + 4 * a_rep + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]))); 0 <= (b_seed + to_integer(n + 4) * a_seed + adler_weighted_sum(bytes, n + 4, n + 4)); (b_rep + 4 * a_rep + (4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]))) == (b_seed + to_integer(n + 4) * a_seed + adler_weighted_sum(bytes, n + 4, n + 4)) + 65521 * (truncating_quotient(b_rep, 65521) - truncating_quotient((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521) + 4 * (truncating_quotient(a_rep, 65521) - truncating_quotient((a_seed + adler_byte_sum(bytes, n)), 65521))); };
  unfold(adler_spec_b(bytes, n + 4, a_seed, b_seed)); assumption();
 }
}
theorem adler_weighted_append_one(bytes: uint8[], n: int32) {
 requires 0 <= n;
 requires n <= 2147483646;
 ensures adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n) + to_integer((int32)bytes[n]) by {
  have 0 < n + 1 by arithmetic() using { 0 <= n; n <= 2147483646; };
  have (n + 1) - 1 == n by arithmetic() using { 0 <= n; n <= 2147483646; };
  apply(adler_weighted_prefix_step(bytes, n + 1)) using { 0 < n + 1; };
  apply(adler_sum_append(bytes, n + 1)) using { 0 < n + 1; };
  rewrite(adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, (n + 1) - 1, (n + 1) - 1) + adler_byte_sum(bytes, n + 1));
  rewrite(adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, (n + 1) - 1) + to_integer((int32)bytes[(n + 1) - 1]));
  rewrite((n + 1) - 1 == n);
  simp();
 }
}

theorem adler_prefix_b_step_one(bytes: uint8[], n: int32, a_seed: Integer, b_seed: Integer, a_rep: Integer, b_rep: Integer) {
 requires 0 <= n;
 requires n <= 2147483646;
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= b_seed;
 requires 0 <= a_rep;
 requires 0 <= b_rep;
 requires truncating_remainder(a_rep, 65521) == adler_spec_a(bytes, n, a_seed);
 requires truncating_remainder(b_rep, 65521) == adler_spec_b(bytes, n, a_seed, b_seed);
 ensures truncating_remainder((b_rep + a_rep + to_integer((int32)bytes[n])), 65521) == adler_spec_b(bytes, n + 1, a_seed, b_seed) by {
  apply(adler_sum_nonnegative(bytes, n));
  apply(adler_weighted_nonnegative(bytes, n));
  apply(adler_weighted_append_one(bytes, n));
  have defined(n + 1) by simp() using { 0 <= n; n <= 2147483646; };
  apply(int32_add_to_integer(n, 1)) using { defined(n + 1); };
  apply(int32_less_equal_to_integer(0, n));
  apply(int32_less_equal_to_integer(n, 2147483646));
  have 0 <= to_integer(n) * a_seed by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(n) => 0 <= to_integer(n);
   premise 1: to_integer(n) <= 2147483646 => to_integer(n) <= 2147483646;
   premise 2: 0 <= a_seed => 0 <= a_seed;
   premise 3: a_seed <= 65520 => a_seed <= 65520;
   integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(n) * a_seed; conclusion 0;
  } }
  have 0 <= (a_seed + adler_byte_sum(bytes, n)) by arithmetic() using { 0 <= a_seed; 0 <= adler_byte_sum(bytes, n); };
  have 0 <= b_seed + to_integer(n) * a_seed by arithmetic() using { 0 <= b_seed; 0 <= to_integer(n) * a_seed; };
  have 0 <= (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) by arithmetic() using { 0 <= b_seed + to_integer(n) * a_seed; 0 <= adler_weighted_sum(bytes, n, n); };
  apply(adler_byte_bounds(bytes[n]));
  have (to_integer(n) + to_integer(1)) * a_seed == to_integer(n) * a_seed + a_seed by { arithmetic_certificate rules { integer_polynomial_identity bounds [] => (to_integer(n) + to_integer(1)) * a_seed == to_integer(n) * a_seed + a_seed; conclusion 0; } }
  have (b_seed + to_integer(n + 1) * a_seed + adler_weighted_sum(bytes, n + 1, n + 1)) == (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) + (a_seed + adler_byte_sum(bytes, n)) + to_integer((int32)bytes[n]) by {
   rewrite(to_integer(n + 1) == to_integer(n) + to_integer(1));
   rewrite((to_integer(n) + to_integer(1)) * a_seed == to_integer(n) * a_seed + a_seed);
   rewrite(adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n) + to_integer((int32)bytes[n])); arithmetic() using {};
  }
  have truncating_remainder(a_rep, 65521) == truncating_remainder((a_seed + adler_byte_sum(bytes, n)), 65521) by { rewrite(truncating_remainder(a_rep, 65521) == adler_spec_a(bytes, n, a_seed)); unfold(adler_spec_a(bytes, n, a_seed)); simp(); }
  have truncating_remainder(b_rep, 65521) == truncating_remainder((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521) by { rewrite(truncating_remainder(b_rep, 65521) == adler_spec_b(bytes, n, a_seed, b_seed)); unfold(adler_spec_b(bytes, n, a_seed, b_seed)); simp(); }
  apply(integer_truncation_identity(a_rep, 65521)) using { 65521 != 0; };
  apply(integer_truncation_identity(b_rep, 65521)) using { 65521 != 0; };
  apply(integer_truncation_identity((a_seed + adler_byte_sum(bytes, n)), 65521)) using { 65521 != 0; };
  apply(integer_truncation_identity((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521)) using { 65521 != 0; };
  have (b_rep + a_rep + to_integer((int32)bytes[n])) == (b_seed + to_integer(n + 1) * a_seed + adler_weighted_sum(bytes, n + 1, n + 1)) + 65521 * (truncating_quotient(b_rep, 65521) - truncating_quotient((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521) + (truncating_quotient(a_rep, 65521) - truncating_quotient((a_seed + adler_byte_sum(bytes, n)), 65521))) by arithmetic() using { a_rep == truncating_quotient(a_rep, 65521) * 65521 + truncating_remainder(a_rep, 65521); b_rep == truncating_quotient(b_rep, 65521) * 65521 + truncating_remainder(b_rep, 65521); (a_seed + adler_byte_sum(bytes, n)) == truncating_quotient((a_seed + adler_byte_sum(bytes, n)), 65521) * 65521 + truncating_remainder((a_seed + adler_byte_sum(bytes, n)), 65521); (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) == truncating_quotient((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521) * 65521 + truncating_remainder((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521); truncating_remainder(a_rep, 65521) == truncating_remainder((a_seed + adler_byte_sum(bytes, n)), 65521); truncating_remainder(b_rep, 65521) == truncating_remainder((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521); (b_seed + to_integer(n + 1) * a_seed + adler_weighted_sum(bytes, n + 1, n + 1)) == (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) + (a_seed + adler_byte_sum(bytes, n)) + to_integer((int32)bytes[n]); };
  have 0 <= b_rep + a_rep by arithmetic() using { 0 <= b_rep; 0 <= a_rep; };
  have 0 <= (b_rep + a_rep + to_integer((int32)bytes[n])) by arithmetic() using { 0 <= b_rep + a_rep; 0 <= to_integer((int32)bytes[n]); };
  have 0 <= (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) + (a_seed + adler_byte_sum(bytes, n)) by arithmetic() using { 0 <= (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)); 0 <= (a_seed + adler_byte_sum(bytes, n)); };
  have 0 <= (b_seed + to_integer(n + 1) * a_seed + adler_weighted_sum(bytes, n + 1, n + 1)) by { rewrite((b_seed + to_integer(n + 1) * a_seed + adler_weighted_sum(bytes, n + 1, n + 1)) == (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) + (a_seed + adler_byte_sum(bytes, n)) + to_integer((int32)bytes[n])); arithmetic() using { 0 <= (b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)) + (a_seed + adler_byte_sum(bytes, n)); 0 <= to_integer((int32)bytes[n]); } }
  apply(adler_residue_congruent((b_rep + a_rep + to_integer((int32)bytes[n])), (b_seed + to_integer(n + 1) * a_seed + adler_weighted_sum(bytes, n + 1, n + 1)), (truncating_quotient(b_rep, 65521) - truncating_quotient((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521) + (truncating_quotient(a_rep, 65521) - truncating_quotient((a_seed + adler_byte_sum(bytes, n)), 65521))))) using { 0 <= n; n <= 2147483646; 0 <= (b_rep + a_rep + to_integer((int32)bytes[n])); 0 <= (b_seed + to_integer(n + 1) * a_seed + adler_weighted_sum(bytes, n + 1, n + 1)); (b_rep + a_rep + to_integer((int32)bytes[n])) == (b_seed + to_integer(n + 1) * a_seed + adler_weighted_sum(bytes, n + 1, n + 1)) + 65521 * (truncating_quotient(b_rep, 65521) - truncating_quotient((b_seed + to_integer(n) * a_seed + adler_weighted_sum(bytes, n, n)), 65521) + (truncating_quotient(a_rep, 65521) - truncating_quotient((a_seed + adler_byte_sum(bytes, n)), 65521))); };
  unfold(adler_spec_b(bytes, n + 1, a_seed, b_seed)); assumption();
 }
}
