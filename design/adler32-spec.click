# Shared Adler-32 specification over a logical byte snapshot.
# The caller supplies a nonnegative signed-range length and canonical seeds.
# These are mathematical lemmas; neither implementation's result is assumed.

function adler_byte_sum(bytes: uint8[], end: int32) -> Integer {
 (0..end).fold(0, |acc, k| { acc + to_integer((int32)bytes[k]) })
}
function adler_weighted_sum(bytes: uint8[], end: int32, weight_end: int32) -> Integer {
 (0..end).fold(0, |acc, k| {
  acc + (to_integer(weight_end) - to_integer(k)) * to_integer((int32)bytes[k])
 })
}
function adler_spec_a(bytes: uint8[], length: int32, a0: Integer) -> Integer {
 truncating_remainder(a0 + adler_byte_sum(bytes, length), 65521)
}
function adler_spec_b(bytes: uint8[], length: int32, a0: Integer, b0: Integer) -> Integer {
 truncating_remainder(b0 + to_integer(length) * a0 + adler_weighted_sum(bytes, length, length), 65521)
}
theorem adler_sum_empty(bytes: uint8[], weight_end: int32) {
 ensures adler_byte_sum(bytes, 0) == 0 by { peel(adler_byte_sum(bytes, 0)) using { 0 >= 0; } simp(); }
 ensures adler_weighted_sum(bytes, 0, weight_end) == 0 by { peel(adler_weighted_sum(bytes, 0, weight_end)) using { 0 >= 0; } simp(); }
}

theorem adler_sum_append(bytes: uint8[], n: int32) {
 requires 0 < n;
 ensures adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]) by {
  have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
  have n - 1 < 2147483647 by { arithmetic() using { 0 < n; } }
  peel(adler_byte_sum(bytes, n)) using { 0 <= n - 1; n - 1 < 2147483647; }
  normalize();
 }
}
theorem adler_weighted_append(bytes: uint8[], n: int32, weight_end: int32) {
 requires 0 < n;
 ensures adler_weighted_sum(bytes, n, weight_end) == adler_weighted_sum(bytes, n - 1, weight_end) + (to_integer(weight_end) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1]) by {
  have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
  have n - 1 < 2147483647 by { arithmetic() using { 0 < n; } }
  peel(adler_weighted_sum(bytes, n, weight_end)) using { 0 <= n - 1; n - 1 < 2147483647; }
  normalize();
 }
}

theorem adler_weight_shift(bytes: uint8[], n: int32, w0: int32, w1: int32) {
 requires 0 <= n;
 ensures adler_weighted_sum(bytes, n, w1) - adler_weighted_sum(bytes, n, w0) == (to_integer(w1) - to_integer(w0)) * adler_byte_sum(bytes, n) by {
  induct(n) as ih;
  if n <= 0 {
   peel(adler_weighted_sum(bytes, n, w1)) using { n <= 0; }
   peel(adler_weighted_sum(bytes, n, w0)) using { n <= 0; }
   peel(adler_byte_sum(bytes, n)) using { n <= 0; }
   have adler_weighted_sum(bytes, n, w1) == 0 by { assumption(); }
   have adler_weighted_sum(bytes, n, w0) == 0 by { assumption(); }
   have adler_byte_sum(bytes, n) == 0 by { assumption(); }
   arithmetic() using { adler_weighted_sum(bytes, n, w1) == 0; adler_weighted_sum(bytes, n, w0) == 0; adler_byte_sum(bytes, n) == 0; }
  } else {
   have 0 < n by { simp(); }
   have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
   have n - 1 < n by { arithmetic() using { 0 < n; } }
   have n - 1 < 2147483647 by { arithmetic() using { 0 < n; } }
   apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; }
   peel(adler_weighted_sum(bytes, n, w1)) using { 0 <= n - 1; n - 1 < 2147483647; }
   peel(adler_weighted_sum(bytes, n, w0)) using { 0 <= n - 1; n - 1 < 2147483647; }
   peel(adler_byte_sum(bytes, n)) using { 0 <= n - 1; n - 1 < 2147483647; }
   have (adler_weighted_sum(bytes, n - 1, w1) + (to_integer(w1) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) - (adler_weighted_sum(bytes, n - 1, w0) + (to_integer(w0) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) == (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (to_integer(w1) - to_integer(w0)) * to_integer((int32)bytes[n - 1]) by {
    arithmetic_certificate rules {
     integer_polynomial_identity bounds [] => (adler_weighted_sum(bytes, n - 1, w1) + (to_integer(w1) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) - (adler_weighted_sum(bytes, n - 1, w0) + (to_integer(w0) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) == (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (to_integer(w1) - to_integer(w0)) * to_integer((int32)bytes[n - 1]);
     conclusion 0;
    }
   }
   rewrite((adler_weighted_sum(bytes, n - 1, w1) + (to_integer(w1) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) - (adler_weighted_sum(bytes, n - 1, w0) + (to_integer(w0) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) == (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (to_integer(w1) - to_integer(w0)) * to_integer((int32)bytes[n - 1]));
   rewrite(adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0) == (to_integer(w1) - to_integer(w0)) * adler_byte_sum(bytes, n - 1));
   arithmetic_certificate rules {
    integer_polynomial_identity bounds [] => (to_integer(w1) - to_integer(w0)) * adler_byte_sum(bytes, n - 1) + (to_integer(w1) - to_integer(w0)) * to_integer((int32)bytes[n - 1]) == (to_integer(w1) - to_integer(w0)) * (adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]));
    conclusion 0;
   }
  }
 }
}

theorem adler_weighted_prefix_step(bytes: uint8[], n: int32) {
 requires 0 < n;
 ensures adler_weighted_sum(bytes, n, n) == adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n) by {
  have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
  have defined(n - 1) by { simp() using { 0 < n; } }
  apply(int32_subtract_to_integer(n, 1)) using { defined(n - 1); }
  have to_integer(n) - to_integer(n - 1) == 1 by { arithmetic() using { to_integer(n - 1) == to_integer(n) - to_integer(1); } }
  apply(adler_weight_shift(bytes, n - 1, n - 1, n)) using { 0 <= n - 1; }
  have adler_byte_sum(bytes, n - 1) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1) by {
   rewrite(to_integer(n) - to_integer(n - 1) == 1);
   arithmetic() using { }
  }
  have adler_weighted_sum(bytes, n - 1, n) == adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n - 1) by {
   rewrite(adler_byte_sum(bytes, n - 1) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1));
   arithmetic() using { adler_weighted_sum(bytes, n - 1, n) - adler_weighted_sum(bytes, n - 1, n - 1) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1); to_integer(n) - to_integer(n - 1) == 1; }
  }
  apply(adler_weighted_append(bytes, n, n)) using { 0 < n; }
  apply(adler_sum_append(bytes, n)) using { 0 < n; }
  rewrite(adler_weighted_sum(bytes, n, n) == adler_weighted_sum(bytes, n - 1, n) + (to_integer(n) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1]));
  rewrite(adler_weighted_sum(bytes, n - 1, n) == adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n - 1));
  rewrite(to_integer(n) - to_integer(n - 1) == 1);
  rewrite(adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]));
  arithmetic() using { }
 }
}

theorem adler_byte_bounds(value: uint8) {
 ensures 0 <= to_integer((int32)value) by {
  have 0 <= (int32)value by { simp(); }
  apply(int32_less_equal_to_integer(0, (int32)value)) using { 0 <= (int32)value; }
  assumption();
 }
 ensures to_integer((int32)value) <= 255 by {
  have (int32)value <= 255 by { simp(); }
  apply(int32_less_equal_to_integer((int32)value, 255)) using { (int32)value <= 255; }
  assumption();
 }
}


theorem adler_sum_nonnegative(bytes: uint8[], n: int32) {
 requires 0 <= n;
 ensures 0 <= adler_byte_sum(bytes, n) by {
  induct(n) as ih;
  if n <= 0 {
   peel(adler_byte_sum(bytes, n)) using { n <= 0; }
   arithmetic() using { adler_byte_sum(bytes, n) == 0; }
  } else {
   have 0 < n by { simp(); }
   have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
   have n - 1 < n by { arithmetic() using { 0 < n; } }
   apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; }
   apply(adler_byte_bounds(bytes[n - 1]));
   apply(adler_sum_append(bytes, n)) using { 0 < n; }
   rewrite(adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]));
   arithmetic() using { 0 <= adler_byte_sum(bytes, n - 1); 0 <= to_integer((int32)bytes[n - 1]); }
  }
 }
}
theorem adler_weighted_nonnegative(bytes: uint8[], n: int32) {
 requires 0 <= n;
 ensures 0 <= adler_weighted_sum(bytes, n, n) by {
  induct(n) as ih;
  if n <= 0 {
   peel(adler_weighted_sum(bytes, n, n)) using { n <= 0; }
   arithmetic() using { adler_weighted_sum(bytes, n, n) == 0; }
  } else {
   have 0 < n by { simp(); }
   have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
   have n - 1 < n by { arithmetic() using { 0 < n; } }
   apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; }
   apply(adler_sum_nonnegative(bytes, n)) using { 0 <= n; }
   apply(adler_weighted_prefix_step(bytes, n)) using { 0 < n; }
   rewrite(adler_weighted_sum(bytes, n, n) == adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n));
   arithmetic() using { 0 <= adler_weighted_sum(bytes, n - 1, n - 1); 0 <= adler_byte_sum(bytes, n); }
  }
 }
}

theorem adler_residue_unique(n: Integer, q: Integer, r: Integer) {
 requires 0 <= n;
 requires n == q * 65521 + r;
 requires 0 <= r;
 requires r <= 65520;
 ensures truncating_remainder(n, 65521) == r by {
  if q < 0 {
   have q <= -1 by { arithmetic() using { q < 0; } }
   have n <= -1 by { arithmetic() using { n == q * 65521 + r; q <= -1; r <= 65520; } }
   have not (0 <= n) by { arithmetic() using { n <= -1; } }
   contradiction(0 <= n);
  } else {
   have 0 <= q by { arithmetic() using { not (q < 0); } }
   have q * 65521 <= n by { arithmetic() using { n == q * 65521 + r; 0 <= r; } }
   have n < (q + 1) * 65521 by { arithmetic() using { n == q * 65521 + r; r <= 65520; } }
   have 0 < q + 1 by { arithmetic() using { 0 <= q; } }
   apply(integer_positive_divisor_quotient_lower(n, 65521, q)) using { 65521 != 0; 1 <= 65521; q * 65521 <= n; }
   apply(integer_positive_divisor_quotient_strict_upper(n, 65521, q + 1)) using { 65521 != 0; 1 <= 65521; 0 < q + 1; n < (q + 1) * 65521; }
   have truncating_quotient(n, 65521) == q by { arithmetic() using { q <= truncating_quotient(n, 65521); truncating_quotient(n, 65521) < q + 1; } }
   apply(integer_truncation_identity(n, 65521)) using { 65521 != 0; }
   arithmetic() using { n == q * 65521 + r; n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); truncating_quotient(n, 65521) == q; }
  }
 }
}

theorem adler_residue_add(n: Integer, m: Integer) {
 requires 0 <= n;
 requires 0 <= m;
 ensures truncating_remainder(n + m, 65521) == truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) by {
  apply(integer_truncation_identity(n, 65521)) using { 65521 != 0; }
  apply(integer_truncation_identity(m, 65521)) using { 65521 != 0; }
  apply(integer_nonnegative_dividend_remainder(n, 65521)) using { 65521 != 0; 0 <= n; }
  apply(integer_nonnegative_dividend_remainder(m, 65521)) using { 65521 != 0; 0 <= m; }
  have 0 <= n + m by { arithmetic() using { 0 <= n; 0 <= m; } }
  have 0 <= truncating_remainder(n, 65521) + truncating_remainder(m, 65521) by { arithmetic() using { 0 <= truncating_remainder(n, 65521); 0 <= truncating_remainder(m, 65521); } }
  apply(integer_truncation_identity(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) using { 65521 != 0; }
  apply(integer_nonnegative_dividend_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) using { 65521 != 0; 0 <= truncating_remainder(n, 65521) + truncating_remainder(m, 65521); }
  apply(integer_positive_divisor_remainder_upper(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) using { 65521 != 0; 0 < 65521; }
  have n + m == (truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) by {
   arithmetic() using { n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); m == truncating_quotient(m, 65521) * 65521 + truncating_remainder(m, 65521); truncating_remainder(n, 65521) + truncating_remainder(m, 65521) == truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521); }
  }
  apply(adler_residue_unique(n + m, truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521), truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521))) using {
   0 <= n + m;
   n + m == (truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521);
   0 <= truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521);
   truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) <= 65520;
  }
  assumption();
 }
}

function adler_spec_checksum(bytes: uint8[], length: int32, a0: Integer, b0: Integer) -> Integer {
 65536 * adler_spec_b(bytes, length, a0, b0) + adler_spec_a(bytes, length, a0)
}

theorem adler_spec_a_canonical(bytes: uint8[], n: int32, a0: Integer) {
 requires 0 <= n;
 requires 0 <= a0;
 ensures 0 <= adler_spec_a(bytes, n, a0) and adler_spec_a(bytes, n, a0) <= 65520 by {
  apply(adler_sum_nonnegative(bytes, n)) using { 0 <= n; }
  have 0 <= a0 + adler_byte_sum(bytes, n) by { arithmetic() using { 0 <= a0; 0 <= adler_byte_sum(bytes, n); } }
  apply(integer_nonnegative_dividend_remainder(a0 + adler_byte_sum(bytes, n), 65521)) using { 65521 != 0; 0 <= a0 + adler_byte_sum(bytes, n); }
  apply(integer_positive_divisor_remainder_upper(a0 + adler_byte_sum(bytes, n), 65521)) using { 65521 != 0; 0 < 65521; }
  unfold(adler_spec_a(bytes, n, a0));
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_spec_b_canonical(bytes: uint8[], n: int32, a0: Integer, b0: Integer) {
 requires 0 <= n;
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures 0 <= adler_spec_b(bytes, n, a0, b0) and adler_spec_b(bytes, n, a0, b0) <= 65520 by {
  apply(adler_weighted_nonnegative(bytes, n)) using { 0 <= n; }
  apply(int32_less_equal_to_integer(0, n)) using { 0 <= n; }
  have n <= 2147483647 by { normalize(); }
  apply(int32_less_equal_to_integer(n, 2147483647)) using { n <= 2147483647; }
  have 0 <= to_integer(n) * a0 by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer(n) => 0 <= to_integer(n);
    premise 1: to_integer(n) <= 2147483647 => to_integer(n) <= 2147483647;
    premise 2: 0 <= a0 => 0 <= a0;
    premise 3: a0 <= 65520 => a0 <= 65520;
    integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(n) * a0;
    conclusion 0;
   }
  }
  have 0 <= b0 + to_integer(n) * a0 by { arithmetic() using { 0 <= b0; 0 <= to_integer(n) * a0; } }
  have 0 <= b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n) by { arithmetic() using { 0 <= b0 + to_integer(n) * a0; 0 <= adler_weighted_sum(bytes, n, n); } }
  apply(integer_nonnegative_dividend_remainder(b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n), 65521)) using { 65521 != 0; 0 <= b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n); }
  apply(integer_positive_divisor_remainder_upper(b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n), 65521)) using { 65521 != 0; 0 < 65521; }
  unfold(adler_spec_b(bytes, n, a0, b0));
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_spec_packing_bounds(bytes: uint8[], n: int32, a0: Integer, b0: Integer) {
 requires 0 <= n;
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures 0 <= adler_spec_checksum(bytes, n, a0, b0) and adler_spec_checksum(bytes, n, a0, b0) <= 4293984240 by {
  apply(adler_spec_a_canonical(bytes, n, a0)) using { 0 <= n; 0 <= a0; }
  apply(adler_spec_b_canonical(bytes, n, a0, b0)) using { 0 <= n; 0 <= a0; a0 <= 65520; 0 <= b0; }
  unfold(adler_spec_checksum(bytes, n, a0, b0));
  both {
   arithmetic() using { 0 <= adler_spec_b(bytes, n, a0, b0); 0 <= adler_spec_a(bytes, n, a0); }
  } and {
   arithmetic() using { adler_spec_b(bytes, n, a0, b0) <= 65520; adler_spec_a(bytes, n, a0) <= 65520; }
  }
 }
}

theorem adler_spec_empty(bytes: uint8[], a0: Integer, b0: Integer) {
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 requires b0 <= 65520;
 ensures adler_spec_a(bytes, 0, a0) == a0 by {
  apply(adler_sum_empty(bytes, 0));
  have a0 == 0 * 65521 + a0 by { arithmetic() using {}; }
  apply(adler_residue_unique(a0, 0, a0)) using { 0 <= a0; a0 == 0 * 65521 + a0; 0 <= a0; a0 <= 65520; }
  unfold(adler_spec_a(bytes, 0, a0));
  rewrite(adler_byte_sum(bytes, 0) == 0);
  simp() using { truncating_remainder(a0, 65521) == a0; }
 }
 ensures adler_spec_b(bytes, 0, a0, b0) == b0 by {
  apply(adler_sum_empty(bytes, 0));
  have b0 == 0 * 65521 + b0 by { arithmetic() using {}; }
  apply(adler_residue_unique(b0, 0, b0)) using { 0 <= b0; b0 == 0 * 65521 + b0; 0 <= b0; b0 <= 65520; }
  unfold(adler_spec_b(bytes, 0, a0, b0));
  rewrite(adler_weighted_sum(bytes, 0, 0) == 0);
  simp() using { truncating_remainder(b0, 65521) == b0; }
 }
}

theorem adler_byte_observation_same_index(bytes: uint8[], i: int32, j: int32) {
 requires i == j;
 ensures to_integer((int32)bytes[i]) == to_integer((int32)bytes[j]) by { rewrite(i == j); normalize(); }
}

theorem adler_sum_append_four(bytes: uint8[], n: int32) {
 requires 0 <= n;
 requires n <= 2147483643;
 ensures adler_byte_sum(bytes, n + 4) == adler_byte_sum(bytes, n) + to_integer((int32)bytes[n]) + to_integer((int32)bytes[n + 1]) + to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]) by {
  have 0 < n + 1 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  have (n + 1) - 1 == n by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  apply(adler_sum_append(bytes, n + 1)) using { 0 < n + 1; }
  have adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + to_integer((int32)bytes[n]) by { simp() using { adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, (n + 1) - 1) + to_integer((int32)bytes[(n + 1) - 1]); (n + 1) - 1 == n; } }
  have 0 < n + 2 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  have (n + 2) - 1 == n + 1 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  apply(adler_sum_append(bytes, n + 2)) using { 0 < n + 2; }
  have n + 1 == (n + 2) - 1 by { simp() using { (n + 2) - 1 == n + 1; } }
  apply(adler_byte_observation_same_index(bytes, n + 1, (n + 2) - 1)) using { n + 1 == (n + 2) - 1; }
  have adler_byte_sum(bytes, n + 2) == adler_byte_sum(bytes, n + 1) + to_integer((int32)bytes[n + 1]) by { rewrite(n + 1 == (n + 2) - 1); rewrite(to_integer((int32)bytes[n + 1]) == to_integer((int32)bytes[(n + 2) - 1])); assumption(); }
  have 0 < n + 3 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  have (n + 3) - 1 == n + 2 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  apply(adler_sum_append(bytes, n + 3)) using { 0 < n + 3; }
  have n + 2 == (n + 3) - 1 by { simp() using { (n + 3) - 1 == n + 2; } }
  apply(adler_byte_observation_same_index(bytes, n + 2, (n + 3) - 1)) using { n + 2 == (n + 3) - 1; }
  have adler_byte_sum(bytes, n + 3) == adler_byte_sum(bytes, n + 2) + to_integer((int32)bytes[n + 2]) by { rewrite(n + 2 == (n + 3) - 1); rewrite(to_integer((int32)bytes[n + 2]) == to_integer((int32)bytes[(n + 3) - 1])); assumption(); }
  have 0 < n + 4 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  have (n + 4) - 1 == n + 3 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  apply(adler_sum_append(bytes, n + 4)) using { 0 < n + 4; }
  have n + 3 == (n + 4) - 1 by { simp() using { (n + 4) - 1 == n + 3; } }
  apply(adler_byte_observation_same_index(bytes, n + 3, (n + 4) - 1)) using { n + 3 == (n + 4) - 1; }
  have adler_byte_sum(bytes, n + 4) == adler_byte_sum(bytes, n + 3) + to_integer((int32)bytes[n + 3]) by { rewrite(n + 3 == (n + 4) - 1); rewrite(to_integer((int32)bytes[n + 3]) == to_integer((int32)bytes[(n + 4) - 1])); assumption(); }
  rewrite(adler_byte_sum(bytes, n + 4) == adler_byte_sum(bytes, n + 3) + to_integer((int32)bytes[n + 3]));
  rewrite(adler_byte_sum(bytes, n + 3) == adler_byte_sum(bytes, n + 2) + to_integer((int32)bytes[n + 2]));
  rewrite(adler_byte_sum(bytes, n + 2) == adler_byte_sum(bytes, n + 1) + to_integer((int32)bytes[n + 1]));
  rewrite(adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + to_integer((int32)bytes[n]));
  arithmetic() using {};
 }
}

theorem adler_weighted_append_four(bytes: uint8[], n: int32) {
 requires 0 <= n;
 requires n <= 2147483643;
 ensures adler_weighted_sum(bytes, n + 4, n + 4) == adler_weighted_sum(bytes, n, n) + 4 * adler_byte_sum(bytes, n) + 4 * to_integer((int32)bytes[n]) + 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2]) + to_integer((int32)bytes[n + 3]) by {
  have 0 < n + 1 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  have (n + 1) - 1 == n by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  apply(adler_sum_append(bytes, n + 1)) using { 0 < n + 1; }
  have adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + to_integer((int32)bytes[n]) by { simp() using { adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, (n + 1) - 1) + to_integer((int32)bytes[(n + 1) - 1]); (n + 1) - 1 == n; } }
  have 0 < n + 2 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  have (n + 2) - 1 == n + 1 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  apply(adler_sum_append(bytes, n + 2)) using { 0 < n + 2; }
  have n + 1 == (n + 2) - 1 by { simp() using { (n + 2) - 1 == n + 1; } }
  apply(adler_byte_observation_same_index(bytes, n + 1, (n + 2) - 1)) using { n + 1 == (n + 2) - 1; }
  have adler_byte_sum(bytes, n + 2) == adler_byte_sum(bytes, n + 1) + to_integer((int32)bytes[n + 1]) by { rewrite(n + 1 == (n + 2) - 1); rewrite(to_integer((int32)bytes[n + 1]) == to_integer((int32)bytes[(n + 2) - 1])); assumption(); }
  have 0 < n + 3 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  have (n + 3) - 1 == n + 2 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  apply(adler_sum_append(bytes, n + 3)) using { 0 < n + 3; }
  have n + 2 == (n + 3) - 1 by { simp() using { (n + 3) - 1 == n + 2; } }
  apply(adler_byte_observation_same_index(bytes, n + 2, (n + 3) - 1)) using { n + 2 == (n + 3) - 1; }
  have adler_byte_sum(bytes, n + 3) == adler_byte_sum(bytes, n + 2) + to_integer((int32)bytes[n + 2]) by { rewrite(n + 2 == (n + 3) - 1); rewrite(to_integer((int32)bytes[n + 2]) == to_integer((int32)bytes[(n + 3) - 1])); assumption(); }
  have 0 < n + 4 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  have (n + 4) - 1 == n + 3 by { arithmetic() using { 0 <= n; n <= 2147483643; } }
  apply(adler_sum_append(bytes, n + 4)) using { 0 < n + 4; }
  have n + 3 == (n + 4) - 1 by { simp() using { (n + 4) - 1 == n + 3; } }
  apply(adler_byte_observation_same_index(bytes, n + 3, (n + 4) - 1)) using { n + 3 == (n + 4) - 1; }
  have adler_byte_sum(bytes, n + 4) == adler_byte_sum(bytes, n + 3) + to_integer((int32)bytes[n + 3]) by { rewrite(n + 3 == (n + 4) - 1); rewrite(to_integer((int32)bytes[n + 3]) == to_integer((int32)bytes[(n + 4) - 1])); assumption(); }
  apply(adler_weighted_prefix_step(bytes, n + 1)) using { 0 < n + 1; }
  have adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n + 1) by { simp() using { adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, (n + 1) - 1, (n + 1) - 1) + adler_byte_sum(bytes, n + 1); (n + 1) - 1 == n; } }
  apply(adler_weighted_prefix_step(bytes, n + 2)) using { 0 < n + 2; }
  have adler_weighted_sum(bytes, n + 2, n + 2) == adler_weighted_sum(bytes, n + 1, n + 1) + adler_byte_sum(bytes, n + 2) by { rewrite(n + 1 == (n + 2) - 1); assumption(); }
  apply(adler_weighted_prefix_step(bytes, n + 3)) using { 0 < n + 3; }
  have adler_weighted_sum(bytes, n + 3, n + 3) == adler_weighted_sum(bytes, n + 2, n + 2) + adler_byte_sum(bytes, n + 3) by { rewrite(n + 2 == (n + 3) - 1); assumption(); }
  apply(adler_weighted_prefix_step(bytes, n + 4)) using { 0 < n + 4; }
  have adler_weighted_sum(bytes, n + 4, n + 4) == adler_weighted_sum(bytes, n + 3, n + 3) + adler_byte_sum(bytes, n + 4) by { rewrite(n + 3 == (n + 4) - 1); assumption(); }
  rewrite(adler_weighted_sum(bytes, n + 4, n + 4) == adler_weighted_sum(bytes, n + 3, n + 3) + adler_byte_sum(bytes, n + 4));
  rewrite(adler_weighted_sum(bytes, n + 3, n + 3) == adler_weighted_sum(bytes, n + 2, n + 2) + adler_byte_sum(bytes, n + 3));
  rewrite(adler_weighted_sum(bytes, n + 2, n + 2) == adler_weighted_sum(bytes, n + 1, n + 1) + adler_byte_sum(bytes, n + 2));
  rewrite(adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n + 1));
  rewrite(adler_byte_sum(bytes, n + 4) == adler_byte_sum(bytes, n + 3) + to_integer((int32)bytes[n + 3]));
  rewrite(adler_byte_sum(bytes, n + 3) == adler_byte_sum(bytes, n + 2) + to_integer((int32)bytes[n + 2]));
  rewrite(adler_byte_sum(bytes, n + 2) == adler_byte_sum(bytes, n + 1) + to_integer((int32)bytes[n + 1]));
  rewrite(adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + to_integer((int32)bytes[n]));
  arithmetic() using {};
 }
}

# A signed quotient difference can witness congruence even when either
# representative is smaller. Both dividend interpretations remain nonnegative.
theorem adler_residue_congruent(n: Integer, m: Integer, q: Integer) {
 requires 0 <= n;
 requires 0 <= m;
 requires n == m + 65521 * q;
 ensures truncating_remainder(n, 65521) == truncating_remainder(m, 65521) by {
  apply(integer_truncation_identity(m, 65521)) using { 65521 != 0; }
  apply(integer_nonnegative_dividend_remainder(m, 65521)) using { 65521 != 0; 0 <= m; }
  apply(integer_positive_divisor_remainder_upper(m, 65521)) using { 65521 != 0; 0 < 65521; }
  have n == (truncating_quotient(m, 65521) + q) * 65521 + truncating_remainder(m, 65521) by {
   arithmetic() using { n == m + 65521 * q; m == truncating_quotient(m, 65521) * 65521 + truncating_remainder(m, 65521); }
  }
  apply(adler_residue_unique(n, truncating_quotient(m, 65521) + q, truncating_remainder(m, 65521))) using {
   0 <= n;
   n == (truncating_quotient(m, 65521) + q) * 65521 + truncating_remainder(m, 65521);
   0 <= truncating_remainder(m, 65521);
   truncating_remainder(m, 65521) <= 65520;
  }
  assumption();
 }
}

theorem adler_spec_one(bytes: uint8[]) {
 ensures adler_spec_a(bytes, 1, 1) == truncating_remainder(1 + to_integer((int32)bytes[0]), 65521) by {
  apply(adler_sum_empty(bytes, 1));
  apply(adler_sum_append(bytes, 1));
  unfold(adler_spec_a(bytes, 1, 1));
  rewrite(adler_byte_sum(bytes, 1) == adler_byte_sum(bytes, 0) + to_integer((int32)bytes[0]));
  rewrite(adler_byte_sum(bytes, 0) == 0);
  simp();
 }
 ensures adler_spec_b(bytes, 1, 1, 0) == truncating_remainder(1 + to_integer((int32)bytes[0]), 65521) by {
  apply(adler_sum_empty(bytes, 1));
  apply(adler_weighted_append(bytes, 1, 1));
  unfold(adler_spec_b(bytes, 1, 1, 0));
  rewrite(adler_weighted_sum(bytes, 1, 1) == adler_weighted_sum(bytes, 0, 1) + to_integer((int32)bytes[0]));
  rewrite(adler_weighted_sum(bytes, 0, 1) == 0);
  simp();
 }
}

theorem adler_byte_offset_association(bytes: uint8[], prefix: int32, suffix: int32) {
 requires defined(prefix + suffix);
 ensures to_integer((int32)(bytes + prefix)[suffix]) == to_integer((int32)bytes[prefix + suffix]) by {
  have (bytes + prefix) + suffix == bytes + (prefix + suffix) by { normalize() using { defined(prefix + suffix); } }
  have (int32)(bytes + prefix)[suffix] == (int32)bytes[prefix + suffix] by {
   rewrite((bytes + prefix) + suffix == bytes + (prefix + suffix)); simp();
  }
  rewrite((int32)(bytes + prefix)[suffix] == (int32)bytes[prefix + suffix]); simp();
 }
}

theorem adler_sum_concat(bytes: uint8[], prefix: int32, suffix: int32) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires prefix <= 2147483647 - suffix;
 requires defined(prefix + suffix);
 ensures adler_byte_sum(bytes, prefix + suffix) == adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix) by {
  induct(suffix) as ih;
  if suffix <= 0 {
   have suffix == 0 by { arithmetic() using { 0 <= suffix; suffix <= 0; } }
   have prefix + suffix == prefix by { rewrite(suffix == 0); normalize(); }
   apply(adler_sum_empty(bytes + prefix, 0));
   have adler_byte_sum(bytes + prefix, suffix) == 0 by { rewrite(suffix == 0); assumption(); }
   rewrite(prefix + suffix == prefix);
   arithmetic() using { adler_byte_sum(bytes + prefix, suffix) == 0; }
  } else {
   have 0 < suffix by { simp(); }
   have 0 <= suffix - 1 by { arithmetic() using { 0 < suffix; } }
   have suffix - 1 < suffix by { arithmetic() using { 0 < suffix; } }
   have 1 <= suffix by { arithmetic() using { 0 < suffix; } }
   apply(int32_nonnegative_subtract_within_value_is_defined(suffix, 1));
   have defined(suffix - 1) by { assumption(); }
   have suffix <= 2147483647 by { simp(); }
   have suffix - 1 <= 2147483647 by { simp(); }
   apply(int32_nonnegative_subtract_within_value_is_defined(2147483647, suffix));
   apply(int32_nonnegative_subtract_within_value_is_defined(2147483647, suffix - 1));
   have defined(2147483647 - suffix) by { assumption(); }
   have defined(2147483647 - (suffix - 1)) by { assumption(); }
   apply(int32_subtract_to_integer(2147483647, suffix));
   apply(int32_subtract_to_integer(2147483647, suffix - 1)) using { defined(2147483647 - (suffix - 1)); }
   apply(int32_subtract_to_integer(suffix, 1)) using { defined(suffix - 1); }
   apply(int32_less_equal_to_integer(prefix, 2147483647 - suffix));
   have to_integer(prefix) <= to_integer(2147483647 - (suffix - 1)) by { arithmetic() using {
    to_integer(prefix) <= to_integer(2147483647 - suffix);
    to_integer(2147483647 - suffix) == to_integer(2147483647) - to_integer(suffix);
    to_integer(2147483647 - (suffix - 1)) == to_integer(2147483647) - to_integer(suffix - 1);
    to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   } }
   apply(int32_to_integer_less_equal_implies_less_equal(prefix, 2147483647 - (suffix - 1)));
   have prefix <= 2147483647 - (suffix - 1) by { assumption(); }
   apply(int32_nonnegative_add_within_max_is_defined(prefix, suffix - 1));
   have defined(prefix + (suffix - 1)) by { assumption(); }
   apply(ih(suffix - 1)) using { 0 <= prefix; 0 <= suffix - 1; suffix - 1 < suffix; prefix <= 2147483647 - (suffix - 1); defined(prefix + (suffix - 1)); }
   have 0 < prefix + suffix by { arithmetic() using { 0 <= prefix; 0 <= suffix; 0 < suffix; prefix <= 2147483647 - suffix; suffix <= 2147483647; defined(prefix + suffix); defined(suffix - 1); 0 <= suffix - 1; defined(2147483647 - suffix); defined(2147483647 - (suffix - 1)); } }
   have 1 <= prefix + suffix by { arithmetic() using { 0 <= prefix; 0 <= suffix; 0 < suffix; prefix <= 2147483647 - suffix; suffix <= 2147483647; defined(prefix + suffix); defined(2147483647 - suffix); } }
   apply(int32_nonnegative_subtract_within_value_is_defined(prefix + suffix, 1));
   have defined((prefix + suffix) - 1) by { assumption(); }
   apply(int32_add_to_integer(prefix, suffix)) using { defined(prefix + suffix); }
   apply(int32_add_to_integer(prefix, suffix - 1)) using { defined(prefix + (suffix - 1)); }
   apply(int32_subtract_to_integer(prefix + suffix, 1)) using { defined((prefix + suffix) - 1); }
   have to_integer((prefix + suffix) - 1) == to_integer(prefix + (suffix - 1)) by { arithmetic() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer(prefix + (suffix - 1)) == to_integer(prefix) + to_integer(suffix - 1);
    to_integer((prefix + suffix) - 1) == to_integer(prefix + suffix) - to_integer(1);
    to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   } }
   apply(int32_to_integer_equal_implies_equal((prefix + suffix) - 1, prefix + (suffix - 1)));
   have (prefix + suffix) - 1 == prefix + (suffix - 1) by { assumption(); }
   apply(adler_sum_append(bytes, prefix + suffix));
   apply(adler_sum_append(bytes + prefix, suffix));
   apply(adler_byte_offset_association(bytes, prefix, suffix - 1)) using { defined(prefix + (suffix - 1)); }
   have adler_byte_sum(bytes, (prefix + suffix) - 1) == adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix - 1) by {
    rewrite((prefix + suffix) - 1 == prefix + (suffix - 1)); assumption();
   }
   have to_integer((int32)bytes[(prefix + suffix) - 1]) == to_integer((int32)(bytes + prefix)[suffix - 1]) by {
    rewrite((prefix + suffix) - 1 == prefix + (suffix - 1)); arithmetic() using { to_integer((int32)(bytes + prefix)[suffix - 1]) == to_integer((int32)bytes[prefix + (suffix - 1)]); }
   }
   arithmetic() using {
    adler_byte_sum(bytes, prefix + suffix) == adler_byte_sum(bytes, (prefix + suffix) - 1) + to_integer((int32)bytes[(prefix + suffix) - 1]);
    adler_byte_sum(bytes + prefix, suffix) == adler_byte_sum(bytes + prefix, suffix - 1) + to_integer((int32)(bytes + prefix)[suffix - 1]);
    adler_byte_sum(bytes, (prefix + suffix) - 1) == adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix - 1);
    to_integer((int32)bytes[(prefix + suffix) - 1]) == to_integer((int32)(bytes + prefix)[suffix - 1]);
   }
  }
 }
}

theorem adler_weighted_concat(bytes: uint8[], prefix: int32, suffix: int32, weight_end: int32) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires prefix <= 2147483647 - suffix;
 requires defined(prefix + suffix);
 requires defined(weight_end - prefix);
 ensures adler_weighted_sum(bytes, prefix + suffix, weight_end) == adler_weighted_sum(bytes, prefix, weight_end) + adler_weighted_sum(bytes + prefix, suffix, weight_end - prefix) by {
  induct(suffix) as ih;
  apply(int32_subtract_to_integer(weight_end, prefix)) using { defined(weight_end - prefix); }
  if suffix <= 0 {
   have suffix == 0 by { arithmetic() using { 0 <= suffix; suffix <= 0; } }
   have prefix + suffix == prefix by { rewrite(suffix == 0); normalize(); }
   apply(adler_sum_empty(bytes + prefix, weight_end - prefix));
   have adler_weighted_sum(bytes + prefix, suffix, weight_end - prefix) == 0 by { rewrite(suffix == 0); assumption(); }
   rewrite(prefix + suffix == prefix);
   arithmetic() using { adler_weighted_sum(bytes + prefix, suffix, weight_end - prefix) == 0; }
  } else {
   have 0 < suffix by { simp(); }
   have 0 <= suffix - 1 by { arithmetic() using { 0 < suffix; } }
   have suffix - 1 < suffix by { arithmetic() using { 0 < suffix; } }
   have 1 <= suffix by { arithmetic() using { 0 < suffix; } }
   apply(int32_nonnegative_subtract_within_value_is_defined(suffix, 1));
   have defined(suffix - 1) by { assumption(); }
   have suffix <= 2147483647 by { simp(); }
   have suffix - 1 <= 2147483647 by { simp(); }
   apply(int32_nonnegative_subtract_within_value_is_defined(2147483647, suffix));
   apply(int32_nonnegative_subtract_within_value_is_defined(2147483647, suffix - 1));
   have defined(2147483647 - suffix) by { assumption(); }
   have defined(2147483647 - (suffix - 1)) by { assumption(); }
   apply(int32_subtract_to_integer(2147483647, suffix));
   apply(int32_subtract_to_integer(2147483647, suffix - 1)) using { defined(2147483647 - (suffix - 1)); }
   apply(int32_subtract_to_integer(suffix, 1)) using { defined(suffix - 1); }
   apply(int32_less_equal_to_integer(prefix, 2147483647 - suffix));
   have to_integer(prefix) <= to_integer(2147483647 - (suffix - 1)) by { arithmetic() using {
    to_integer(prefix) <= to_integer(2147483647 - suffix);
    to_integer(2147483647 - suffix) == to_integer(2147483647) - to_integer(suffix);
    to_integer(2147483647 - (suffix - 1)) == to_integer(2147483647) - to_integer(suffix - 1);
    to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   } }
   apply(int32_to_integer_less_equal_implies_less_equal(prefix, 2147483647 - (suffix - 1)));
   have prefix <= 2147483647 - (suffix - 1) by { assumption(); }
   apply(int32_nonnegative_add_within_max_is_defined(prefix, suffix - 1));
   have defined(prefix + (suffix - 1)) by { assumption(); }
   apply(ih(suffix - 1)) using { 0 <= prefix; 0 <= suffix - 1; suffix - 1 < suffix; defined(weight_end - prefix); prefix <= 2147483647 - (suffix - 1); defined(prefix + (suffix - 1)); }
   have 0 < prefix + suffix by { arithmetic() using { 0 <= prefix; 0 <= suffix; 0 < suffix; prefix <= 2147483647 - suffix; suffix <= 2147483647; defined(prefix + suffix); defined(suffix - 1); 0 <= suffix - 1; defined(2147483647 - suffix); defined(2147483647 - (suffix - 1)); } }
   have 1 <= prefix + suffix by { arithmetic() using { 0 <= prefix; 0 <= suffix; 0 < suffix; prefix <= 2147483647 - suffix; suffix <= 2147483647; defined(prefix + suffix); defined(2147483647 - suffix); } }
   apply(int32_nonnegative_subtract_within_value_is_defined(prefix + suffix, 1));
   have defined((prefix + suffix) - 1) by { assumption(); }
   apply(int32_add_to_integer(prefix, suffix)) using { defined(prefix + suffix); }
   apply(int32_add_to_integer(prefix, suffix - 1)) using { defined(prefix + (suffix - 1)); }
   apply(int32_subtract_to_integer(prefix + suffix, 1)) using { defined((prefix + suffix) - 1); }
   have to_integer((prefix + suffix) - 1) == to_integer(prefix + (suffix - 1)) by { arithmetic() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer(prefix + (suffix - 1)) == to_integer(prefix) + to_integer(suffix - 1);
    to_integer((prefix + suffix) - 1) == to_integer(prefix + suffix) - to_integer(1);
    to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   } }
   apply(int32_to_integer_equal_implies_equal((prefix + suffix) - 1, prefix + (suffix - 1)));
   have (prefix + suffix) - 1 == prefix + (suffix - 1) by { assumption(); }
   apply(adler_weighted_append(bytes, prefix + suffix, weight_end));
   apply(adler_weighted_append(bytes + prefix, suffix, weight_end - prefix));
   apply(adler_byte_offset_association(bytes, prefix, suffix - 1)) using { defined(prefix + (suffix - 1)); }
   have adler_weighted_sum(bytes, (prefix + suffix) - 1, weight_end) == adler_weighted_sum(bytes, prefix, weight_end) + adler_weighted_sum(bytes + prefix, suffix - 1, weight_end - prefix) by {
    rewrite((prefix + suffix) - 1 == prefix + (suffix - 1)); assumption();
   }
   have to_integer((int32)bytes[(prefix + suffix) - 1]) == to_integer((int32)(bytes + prefix)[suffix - 1]) by {
    rewrite((prefix + suffix) - 1 == prefix + (suffix - 1)); arithmetic() using { to_integer((int32)(bytes + prefix)[suffix - 1]) == to_integer((int32)bytes[prefix + (suffix - 1)]); }
   }
   have to_integer(weight_end) - to_integer((prefix + suffix) - 1) == to_integer(weight_end - prefix) - to_integer(suffix - 1) by { arithmetic() using {
    to_integer(weight_end - prefix) == to_integer(weight_end) - to_integer(prefix);
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer((prefix + suffix) - 1) == to_integer(prefix + suffix) - to_integer(1);
    to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   } }
   have (to_integer(weight_end) - to_integer((prefix + suffix) - 1)) * to_integer((int32)bytes[(prefix + suffix) - 1]) == (to_integer(weight_end - prefix) - to_integer(suffix - 1)) * to_integer((int32)(bytes + prefix)[suffix - 1]) by {
    rewrite(to_integer(weight_end) - to_integer((prefix + suffix) - 1) == to_integer(weight_end - prefix) - to_integer(suffix - 1));
    rewrite(to_integer((int32)bytes[(prefix + suffix) - 1]) == to_integer((int32)(bytes + prefix)[suffix - 1]));
    simp();
   }
   arithmetic() using {
    adler_weighted_sum(bytes, prefix + suffix, weight_end) == adler_weighted_sum(bytes, (prefix + suffix) - 1, weight_end) + (to_integer(weight_end) - to_integer((prefix + suffix) - 1)) * to_integer((int32)bytes[(prefix + suffix) - 1]);
    adler_weighted_sum(bytes + prefix, suffix, weight_end - prefix) == adler_weighted_sum(bytes + prefix, suffix - 1, weight_end - prefix) + (to_integer(weight_end - prefix) - to_integer(suffix - 1)) * to_integer((int32)(bytes + prefix)[suffix - 1]);
    adler_weighted_sum(bytes, (prefix + suffix) - 1, weight_end) == adler_weighted_sum(bytes, prefix, weight_end) + adler_weighted_sum(bytes + prefix, suffix - 1, weight_end - prefix);
    to_integer((int32)bytes[(prefix + suffix) - 1]) == to_integer((int32)(bytes + prefix)[suffix - 1]);
    to_integer(weight_end) - to_integer((prefix + suffix) - 1) == to_integer(weight_end - prefix) - to_integer(suffix - 1);
    (to_integer(weight_end) - to_integer((prefix + suffix) - 1)) * to_integer((int32)bytes[(prefix + suffix) - 1]) == (to_integer(weight_end - prefix) - to_integer(suffix - 1)) * to_integer((int32)(bytes + prefix)[suffix - 1]);
   }
  }
 }
}

theorem adler_residue_add_left(n: Integer, m: Integer) {
 requires 0 <= n;
 requires 0 <= m;
 ensures truncating_remainder(n + m, 65521) == truncating_remainder(truncating_remainder(n, 65521) + m, 65521) by {
  apply(integer_truncation_identity(n, 65521)) using { 65521 != 0; }
  apply(integer_nonnegative_dividend_remainder(n, 65521)) using { 65521 != 0; 0 <= n; }
  have 0 <= n + m by { arithmetic() using { 0 <= n; 0 <= m; } }
  have 0 <= truncating_remainder(n, 65521) + m by { arithmetic() using { 0 <= truncating_remainder(n, 65521); 0 <= m; } }
  have n + m == (truncating_remainder(n, 65521) + m) + 65521 * truncating_quotient(n, 65521) by { arithmetic() using { n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); } }
  apply(adler_residue_congruent(n + m, truncating_remainder(n, 65521) + m, truncating_quotient(n, 65521)));
  assumption();
 }
}

theorem adler_spec_a_concat(bytes: uint8[], prefix: int32, suffix: int32, a0: Integer) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires prefix <= 2147483647 - suffix;
 requires defined(prefix + suffix);
 requires 0 <= a0;
 ensures adler_spec_a(bytes, prefix + suffix, a0) == adler_spec_a(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0)) by {
  apply(adler_sum_concat(bytes, prefix, suffix));
  apply(adler_sum_nonnegative(bytes, prefix));
  apply(adler_sum_nonnegative(bytes + prefix, suffix));
  have 0 <= a0 + adler_byte_sum(bytes, prefix) by { arithmetic() using { 0 <= a0; 0 <= adler_byte_sum(bytes, prefix); } }
  apply(adler_residue_add_left(a0 + adler_byte_sum(bytes, prefix), adler_byte_sum(bytes + prefix, suffix)));
  unfold(adler_spec_a(bytes, prefix + suffix, a0));
  unfold(adler_spec_a(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0)));
  unfold(adler_spec_a(bytes, prefix, a0));
  rewrite(adler_byte_sum(bytes, prefix + suffix) == adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix));
  have a0 + (adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix)) == (a0 + adler_byte_sum(bytes, prefix)) + adler_byte_sum(bytes + prefix, suffix) by { arithmetic() using {}; }
  rewrite(a0 + (adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix)) == (a0 + adler_byte_sum(bytes, prefix)) + adler_byte_sum(bytes + prefix, suffix));
  assumption();
 }
}

theorem adler_sum_upper(bytes: uint8[], n: int32) {
 requires 0 <= n;
 ensures adler_byte_sum(bytes, n) <= 255 * to_integer(n) by {
  induct(n) as ih;
  if n <= 0 {
   have n == 0 by { arithmetic() using { 0 <= n; n <= 0; } }
   apply(adler_sum_empty(bytes, 0));
   rewrite(n == 0);
   arithmetic() using { adler_byte_sum(bytes, 0) == 0; }
  } else {
   have 0 < n by { simp(); }
   have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
   have n - 1 < n by { arithmetic() using { 0 < n; } }
   apply(ih(n - 1));
   apply(adler_sum_append(bytes, n));
   apply(adler_byte_bounds(bytes[n - 1]));
   have defined(n - 1) by { simp(); }
   apply(int32_subtract_to_integer(n, 1)) using { defined(n - 1); }
   arithmetic() using {
    adler_byte_sum(bytes, n - 1) <= 255 * to_integer(n - 1);
    adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]);
    to_integer((int32)bytes[n - 1]) <= 255;
    to_integer(n - 1) == to_integer(n) - to_integer(1);
   }
  }
 }
}

theorem adler_seed_polynomial(x: Integer, y: Integer, k: Integer, z: Integer, qa: Integer, ra: Integer, qb: Integer, rb: Integer) {
 requires x == qa * 65521 + ra;
 requires y == qb * 65521 + rb;
 ensures y + k * x + z == (rb + k * ra + z) + 65521 * (qb + k * qa) by {
  rewrite(y == qb * 65521 + rb);
  rewrite(x == qa * 65521 + ra);
  arithmetic_certificate rules {
   integer_polynomial_identity bounds [] => (qb * 65521 + rb) + k * (qa * 65521 + ra) + z == (rb + k * ra + z) + 65521 * (qb + k * qa); conclusion 0;
  }
 }
}

theorem adler_residue_seed_update(x: Integer, y: Integer, k: Integer, z: Integer) {
 requires 0 <= x;
 requires x <= 549755879424;
 requires 0 <= y;
 requires 0 <= k;
 requires k <= 2147483647;
 requires 0 <= z;
 ensures truncating_remainder(y + k * x + z, 65521) == truncating_remainder(truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z, 65521) by {
  apply(integer_truncation_identity(x, 65521)) using { 65521 != 0; }
  apply(integer_truncation_identity(y, 65521)) using { 65521 != 0; }
  apply(integer_nonnegative_dividend_remainder(x, 65521)) using { 65521 != 0; 0 <= x; }
  apply(integer_nonnegative_dividend_remainder(y, 65521)) using { 65521 != 0; 0 <= y; }
  apply(integer_positive_divisor_remainder_upper(x, 65521)) using { 65521 != 0; 0 < 65521; }
  have 0 <= k * x by { arithmetic_certificate rules {
   premise 0: 0 <= k => 0 <= k;
   premise 1: k <= 2147483647 => k <= 2147483647;
   premise 2: 0 <= x => 0 <= x;
   premise 3: x <= 549755879424 => x <= 549755879424;
   integer_product_bounds bounds [0, 1, 2, 3] => 0 <= k * x; conclusion 0;
  } }
  have 0 <= k * truncating_remainder(x, 65521) by { arithmetic_certificate rules {
   premise 0: 0 <= k => 0 <= k;
   premise 1: k <= 2147483647 => k <= 2147483647;
   premise 2: 0 <= truncating_remainder(x, 65521) => 0 <= truncating_remainder(x, 65521);
   premise 3: truncating_remainder(x, 65521) <= 65520 => truncating_remainder(x, 65521) <= 65520;
   integer_product_bounds bounds [0, 1, 2, 3] => 0 <= k * truncating_remainder(x, 65521); conclusion 0;
  } }
  have 0 <= y + k * x + z by { arithmetic_certificate {
   premise 0: 0 <= y => 0 <= y;
   premise 1: 0 <= k * x => 0 <= k * x;
   premise 2: 0 <= z => 0 <= z;
   add 0, 1 => 0 <= y + k * x;
   add 3, 2 => 0 <= y + k * x + z; conclusion 4;
  } }
  have 0 <= truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z by { arithmetic_certificate {
   premise 0: 0 <= truncating_remainder(y, 65521) => 0 <= truncating_remainder(y, 65521);
   premise 1: 0 <= k * truncating_remainder(x, 65521) => 0 <= k * truncating_remainder(x, 65521);
   premise 2: 0 <= z => 0 <= z;
   add 0, 1 => 0 <= truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521);
   add 3, 2 => 0 <= truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z; conclusion 4;
  } }
  apply(adler_seed_polynomial(x, y, k, z, truncating_quotient(x, 65521), truncating_remainder(x, 65521), truncating_quotient(y, 65521), truncating_remainder(y, 65521)));
  apply(adler_residue_congruent(y + k * x + z, truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z, truncating_quotient(y, 65521) + k * truncating_quotient(x, 65521)));
  assumption();
 }
}

theorem adler_concat_index_partition(prefix: int32, suffix: int32) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires prefix <= 2147483647 - suffix;
 requires defined(prefix + suffix);
 ensures defined((prefix + suffix) - prefix) and (prefix + suffix) - prefix == suffix by {
  apply(int32_add_to_integer(prefix, suffix)) using { defined(prefix + suffix); }
  apply(int32_less_equal_to_integer(0, suffix));
  have to_integer(prefix) <= to_integer(prefix + suffix) by { arithmetic() using {
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
   to_integer(0) <= to_integer(suffix);
  } }
  apply(int32_to_integer_less_equal_implies_less_equal(prefix, prefix + suffix));
  have prefix <= prefix + suffix by { assumption(); }
  apply(int32_nonnegative_subtract_within_value_is_defined(prefix + suffix, prefix));
  have defined((prefix + suffix) - prefix) by { assumption(); }
  apply(int32_subtract_to_integer(prefix + suffix, prefix)) using { defined((prefix + suffix) - prefix); }
  have to_integer((prefix + suffix) - prefix) == to_integer(suffix) by { arithmetic() using {
   to_integer((prefix + suffix) - prefix) == to_integer(prefix + suffix) - to_integer(prefix);
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  } }
  apply(int32_to_integer_equal_implies_equal((prefix + suffix) - prefix, suffix));
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_weighted_prefix_concat(bytes: uint8[], prefix: int32, suffix: int32) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires prefix <= 2147483647 - suffix;
 requires defined(prefix + suffix);
 ensures adler_weighted_sum(bytes, prefix + suffix, prefix + suffix) == adler_weighted_sum(bytes, prefix, prefix) + to_integer(suffix) * adler_byte_sum(bytes, prefix) + adler_weighted_sum(bytes + prefix, suffix, suffix) by {
  apply(adler_concat_index_partition(prefix, suffix));
  have defined((prefix + suffix) - prefix) by { assumption(); }
  have (prefix + suffix) - prefix == suffix by { assumption(); }
  apply(adler_weighted_concat(bytes, prefix, suffix, prefix + suffix)) using {
   0 <= prefix; 0 <= suffix; prefix <= 2147483647 - suffix;
   defined(prefix + suffix); defined((prefix + suffix) - prefix);
  }
  have adler_weighted_sum(bytes, prefix + suffix, prefix + suffix) == adler_weighted_sum(bytes, prefix, prefix + suffix) + adler_weighted_sum(bytes + prefix, suffix, suffix) by {
   rewrite(suffix == (prefix + suffix) - prefix);
   assumption();
  }
  apply(adler_weight_shift(bytes, prefix, prefix, prefix + suffix));
  apply(int32_add_to_integer(prefix, suffix)) using { defined(prefix + suffix); }
  have to_integer(prefix + suffix) - to_integer(prefix) == to_integer(suffix) by { arithmetic() using {
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  } }
  have adler_weighted_sum(bytes, prefix, prefix + suffix) - adler_weighted_sum(bytes, prefix, prefix) == to_integer(suffix) * adler_byte_sum(bytes, prefix) by {
   rewrite(to_integer(suffix) == to_integer(prefix + suffix) - to_integer(prefix));
   assumption();
  }
  arithmetic() using {
   adler_weighted_sum(bytes, prefix + suffix, prefix + suffix) == adler_weighted_sum(bytes, prefix, prefix + suffix) + adler_weighted_sum(bytes + prefix, suffix, suffix);
   adler_weighted_sum(bytes, prefix, prefix + suffix) - adler_weighted_sum(bytes, prefix, prefix) == to_integer(suffix) * adler_byte_sum(bytes, prefix);
  }
 }
}

theorem adler_join_seed_polynomial(a0: Integer, b0: Integer, p: Integer, s: Integer, sp: Integer, wp: Integer, wt: Integer) {
 ensures b0 + (p + s) * a0 + (wp + s * sp + wt) == (b0 + p * a0 + wp) + s * (a0 + sp) + wt by {
  arithmetic_certificate rules {
   integer_polynomial_identity bounds [] => b0 + (p + s) * a0 + (wp + s * sp + wt) == (b0 + p * a0 + wp) + s * (a0 + sp) + wt; conclusion 0;
  }
 }
}

theorem adler_spec_b_concat(bytes: uint8[], prefix: int32, suffix: int32, a0: Integer, b0: Integer) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires prefix <= 2147483647 - suffix;
 requires defined(prefix + suffix);
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures adler_spec_b(bytes, prefix + suffix, a0, b0) == adler_spec_b(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)) by {
  apply(adler_weighted_prefix_concat(bytes, prefix, suffix));
  apply(adler_sum_nonnegative(bytes, prefix));
  apply(adler_sum_upper(bytes, prefix));
  apply(adler_weighted_nonnegative(bytes, prefix));
  apply(adler_weighted_nonnegative(bytes + prefix, suffix));
  apply(int32_less_equal_to_integer(0, prefix));
  apply(int32_less_equal_to_integer(0, suffix));
  have prefix <= 2147483647 by { normalize(); }
  have suffix <= 2147483647 by { normalize(); }
  apply(int32_less_equal_to_integer(prefix, 2147483647));
  apply(int32_less_equal_to_integer(suffix, 2147483647));
  have 0 <= to_integer(prefix) by { simp() using { to_integer(0) <= to_integer(prefix); } }
  have to_integer(prefix) <= 2147483647 by { simp() using { to_integer(prefix) <= to_integer(2147483647); } }
  have 0 <= to_integer(prefix) * a0 by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(prefix) => 0 <= to_integer(prefix);
   premise 1: to_integer(prefix) <= 2147483647 => to_integer(prefix) <= 2147483647;
   premise 2: 0 <= a0 => 0 <= a0;
   premise 3: a0 <= 65520 => a0 <= 65520;
   integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(prefix) * a0; conclusion 0;
  } }
  have 0 <= a0 + adler_byte_sum(bytes, prefix) by { arithmetic() using { 0 <= a0; 0 <= adler_byte_sum(bytes, prefix); } }
  have 255 * to_integer(prefix) <= 547608329985 by { arithmetic_certificate {
   premise 0: to_integer(prefix) <= 2147483647 => to_integer(prefix) <= 2147483647;
   scale 0 by 255 => 255 * to_integer(prefix) <= 255 * 2147483647; conclusion 1;
  } }
  have adler_byte_sum(bytes, prefix) <= 547608329985 by { arithmetic() using {
   adler_byte_sum(bytes, prefix) <= 255 * to_integer(prefix);
   255 * to_integer(prefix) <= 547608329985;
  } }
  have a0 + adler_byte_sum(bytes, prefix) <= 549755879424 by { arithmetic() using {
   a0 <= 65520; adler_byte_sum(bytes, prefix) <= 547608329985;
  } }
  have 0 <= b0 + to_integer(prefix) * a0 + adler_weighted_sum(bytes, prefix, prefix) by { arithmetic_certificate {
   premise 0: 0 <= b0 => 0 <= b0;
   premise 1: 0 <= to_integer(prefix) * a0 => 0 <= to_integer(prefix) * a0;
   premise 2: 0 <= adler_weighted_sum(bytes, prefix, prefix) => 0 <= adler_weighted_sum(bytes, prefix, prefix);
   add 0, 1 => 0 <= b0 + to_integer(prefix) * a0;
   add 3, 2 => 0 <= b0 + to_integer(prefix) * a0 + adler_weighted_sum(bytes, prefix, prefix); conclusion 4;
  } }
  have 0 <= to_integer(suffix) by { simp() using { to_integer(0) <= to_integer(suffix); } }
  have to_integer(suffix) <= 2147483647 by { simp() using { to_integer(suffix) <= to_integer(2147483647); } }
  apply(adler_residue_seed_update(a0 + adler_byte_sum(bytes, prefix), b0 + to_integer(prefix) * a0 + adler_weighted_sum(bytes, prefix, prefix), to_integer(suffix), adler_weighted_sum(bytes + prefix, suffix, suffix)));
  apply(int32_add_to_integer(prefix, suffix)) using { defined(prefix + suffix); }
  apply(adler_join_seed_polynomial(a0, b0, to_integer(prefix), to_integer(suffix), adler_byte_sum(bytes, prefix), adler_weighted_sum(bytes, prefix, prefix), adler_weighted_sum(bytes + prefix, suffix, suffix)));
  unfold(adler_spec_b(bytes, prefix + suffix, a0, b0));
  unfold(adler_spec_b(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)));
  unfold(adler_spec_a(bytes, prefix, a0));
  unfold(adler_spec_b(bytes, prefix, a0, b0));
  rewrite(adler_weighted_sum(bytes, prefix + suffix, prefix + suffix) == adler_weighted_sum(bytes, prefix, prefix) + to_integer(suffix) * adler_byte_sum(bytes, prefix) + adler_weighted_sum(bytes + prefix, suffix, suffix));
  rewrite(to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix));
  rewrite(b0 + (to_integer(prefix) + to_integer(suffix)) * a0 + (adler_weighted_sum(bytes, prefix, prefix) + to_integer(suffix) * adler_byte_sum(bytes, prefix) + adler_weighted_sum(bytes + prefix, suffix, suffix)) == (b0 + to_integer(prefix) * a0 + adler_weighted_sum(bytes, prefix, prefix)) + to_integer(suffix) * (a0 + adler_byte_sum(bytes, prefix)) + adler_weighted_sum(bytes + prefix, suffix, suffix));
  assumption();
 }
}

theorem adler_spec_checksum_concat(bytes: uint8[], prefix: int32, suffix: int32, a0: Integer, b0: Integer) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires prefix <= 2147483647 - suffix;
 requires defined(prefix + suffix);
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures adler_spec_checksum(bytes, prefix + suffix, a0, b0) == adler_spec_checksum(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)) by {
  apply(adler_spec_a_concat(bytes, prefix, suffix, a0));
  apply(adler_spec_b_concat(bytes, prefix, suffix, a0, b0));
  unfold(adler_spec_checksum(bytes, prefix + suffix, a0, b0));
  unfold(adler_spec_checksum(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)));
  rewrite(adler_spec_a(bytes, prefix + suffix, a0) == adler_spec_a(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0)));
  rewrite(adler_spec_b(bytes, prefix + suffix, a0, b0) == adler_spec_b(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)));
  simp();
 }
}

theorem adler_spec_four(bytes: uint8[]) {
 ensures adler_spec_a(bytes, 4, 1) == truncating_remainder(1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) + to_integer((int32)bytes[3]), 65521) by {
  apply(adler_sum_empty(bytes, 0));
  apply(adler_sum_append_four(bytes, 0));
  have 1 + (to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) + to_integer((int32)bytes[3])) == 1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) + to_integer((int32)bytes[3]) by { arithmetic() using {}; }
  unfold(adler_spec_a(bytes, 4, 1));
  rewrite(adler_byte_sum(bytes, 4) == adler_byte_sum(bytes, 0) + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) + to_integer((int32)bytes[3]));
  rewrite(adler_byte_sum(bytes, 0) == 0);
  rewrite(1 + (to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) + to_integer((int32)bytes[3])) == 1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) + to_integer((int32)bytes[3])); simp();
 }
 ensures adler_spec_b(bytes, 4, 1, 0) == truncating_remainder(4 + 4 * to_integer((int32)bytes[0]) + 3 * to_integer((int32)bytes[1]) + 2 * to_integer((int32)bytes[2]) + to_integer((int32)bytes[3]), 65521) by {
  apply(adler_sum_empty(bytes, 0));
  apply(adler_weighted_append_four(bytes, 0));
  have 4 + (4 * to_integer((int32)bytes[0]) + 3 * to_integer((int32)bytes[1]) + 2 * to_integer((int32)bytes[2]) + to_integer((int32)bytes[3])) == 4 + 4 * to_integer((int32)bytes[0]) + 3 * to_integer((int32)bytes[1]) + 2 * to_integer((int32)bytes[2]) + to_integer((int32)bytes[3]) by { arithmetic() using {}; }
  unfold(adler_spec_b(bytes, 4, 1, 0));
  rewrite(adler_weighted_sum(bytes, 4, 4) == adler_weighted_sum(bytes, 0, 0) + 4 * adler_byte_sum(bytes, 0) + 4 * to_integer((int32)bytes[0]) + 3 * to_integer((int32)bytes[1]) + 2 * to_integer((int32)bytes[2]) + to_integer((int32)bytes[3]));
  rewrite(adler_weighted_sum(bytes, 0, 0) == 0);
  rewrite(adler_byte_sum(bytes, 0) == 0);
  rewrite(4 + (4 * to_integer((int32)bytes[0]) + 3 * to_integer((int32)bytes[1]) + 2 * to_integer((int32)bytes[2]) + to_integer((int32)bytes[3])) == 4 + 4 * to_integer((int32)bytes[0]) + 3 * to_integer((int32)bytes[1]) + 2 * to_integer((int32)bytes[2]) + to_integer((int32)bytes[3])); simp();
 }
}

theorem adler_spec_two(bytes: uint8[]) {
 ensures adler_spec_a(bytes, 2, 1) == truncating_remainder(1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]), 65521) by {
  apply(adler_sum_empty(bytes, 2));
  apply(adler_sum_append(bytes, 1));
  apply(adler_sum_append(bytes, 2));
  have adler_byte_sum(bytes, 2) == to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) by { arithmetic() using { adler_byte_sum(bytes, 0) == 0; adler_byte_sum(bytes, 1) == adler_byte_sum(bytes, 0) + to_integer((int32)bytes[0]); adler_byte_sum(bytes, 2) == adler_byte_sum(bytes, 1) + to_integer((int32)bytes[1]); } }
  have 1 + (to_integer((int32)bytes[0]) + to_integer((int32)bytes[1])) == 1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) by { arithmetic() using {} }
  unfold(adler_spec_a(bytes, 2, 1));
  rewrite(adler_byte_sum(bytes, 2) == to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]));
  rewrite(1 + (to_integer((int32)bytes[0]) + to_integer((int32)bytes[1])) == 1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]));
  simp();
 }
 ensures adler_spec_b(bytes, 2, 1, 0) == truncating_remainder(2 + 2 * to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]), 65521) by {
  apply(adler_sum_empty(bytes, 2));
  apply(adler_weighted_append(bytes, 1, 2));
  apply(adler_weighted_append(bytes, 2, 2));
  have adler_weighted_sum(bytes, 2, 2) == 2 * to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) by { arithmetic() using { adler_weighted_sum(bytes, 0, 2) == 0; adler_weighted_sum(bytes, 1, 2) == adler_weighted_sum(bytes, 0, 2) + 2 * to_integer((int32)bytes[0]); adler_weighted_sum(bytes, 2, 2) == adler_weighted_sum(bytes, 1, 2) + 1 * to_integer((int32)bytes[1]); } }
  have 2 + (2 * to_integer((int32)bytes[0]) + to_integer((int32)bytes[1])) == 2 + 2 * to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) by { arithmetic() using {} }
  unfold(adler_spec_b(bytes, 2, 1, 0));
  rewrite(adler_weighted_sum(bytes, 2, 2) == 2 * to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]));
  rewrite(2 + (2 * to_integer((int32)bytes[0]) + to_integer((int32)bytes[1])) == 2 + 2 * to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]));
  simp();
 }
}

theorem adler_spec_three(bytes: uint8[]) {
 ensures adler_spec_a(bytes, 3, 1) == truncating_remainder(1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]), 65521) by {
  apply(adler_sum_empty(bytes, 3));
  apply(adler_sum_append(bytes, 1));
  apply(adler_sum_append(bytes, 2));
  apply(adler_sum_append(bytes, 3));
  have adler_byte_sum(bytes, 3) == to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) by { arithmetic() using { adler_byte_sum(bytes, 0) == 0; adler_byte_sum(bytes, 1) == adler_byte_sum(bytes, 0) + to_integer((int32)bytes[0]); adler_byte_sum(bytes, 2) == adler_byte_sum(bytes, 1) + to_integer((int32)bytes[1]); adler_byte_sum(bytes, 3) == adler_byte_sum(bytes, 2) + to_integer((int32)bytes[2]); } }
  have 1 + (to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2])) == 1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) by { arithmetic() using {} }
  unfold(adler_spec_a(bytes, 3, 1));
  rewrite(adler_byte_sum(bytes, 3) == to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]));
  rewrite(1 + (to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2])) == 1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]));
  simp();
 }
 ensures adler_spec_b(bytes, 3, 1, 0) == truncating_remainder(3 + 3 * to_integer((int32)bytes[0]) + 2 * to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]), 65521) by {
  apply(adler_sum_empty(bytes, 3));
  apply(adler_weighted_append(bytes, 1, 3));
  apply(adler_weighted_append(bytes, 2, 3));
  apply(adler_weighted_append(bytes, 3, 3));
  have adler_weighted_sum(bytes, 3, 3) == 3 * to_integer((int32)bytes[0]) + 2 * to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) by { arithmetic() using { adler_weighted_sum(bytes, 0, 3) == 0; adler_weighted_sum(bytes, 1, 3) == adler_weighted_sum(bytes, 0, 3) + 3 * to_integer((int32)bytes[0]); adler_weighted_sum(bytes, 2, 3) == adler_weighted_sum(bytes, 1, 3) + 2 * to_integer((int32)bytes[1]); adler_weighted_sum(bytes, 3, 3) == adler_weighted_sum(bytes, 2, 3) + 1 * to_integer((int32)bytes[2]); } }
  have 3 + (3 * to_integer((int32)bytes[0]) + 2 * to_integer((int32)bytes[1]) + to_integer((int32)bytes[2])) == 3 + 3 * to_integer((int32)bytes[0]) + 2 * to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) by { arithmetic() using {} }
  unfold(adler_spec_b(bytes, 3, 1, 0));
  rewrite(adler_weighted_sum(bytes, 3, 3) == 3 * to_integer((int32)bytes[0]) + 2 * to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]));
  rewrite(3 + (3 * to_integer((int32)bytes[0]) + 2 * to_integer((int32)bytes[1]) + to_integer((int32)bytes[2])) == 3 + 3 * to_integer((int32)bytes[0]) + 2 * to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]));
  simp();
 }
}

# Extensionality uses only equality of the selected input bytes; it grants no memory authority.
theorem adler_sums_extensional(left: uint8[], right: uint8[], bound: int32, n: int32, weight: int32) {
 requires 0 <= n;
 requires n <= bound;
 requires forall (k: int32) { 0 <= k and k < bound implies left[k] == right[k] };
 ensures adler_byte_sum(left, n) == adler_byte_sum(right, n) and adler_weighted_sum(left, n, weight) == adler_weighted_sum(right, n, weight) by {
  induct(n) as ih;
  if n <= 0 {
   apply(adler_sum_empty(left, weight));
   apply(adler_sum_empty(right, weight));
   have n == 0 by arithmetic() using { 0 <= n; n <= 0; };
   rewrite(n == 0);
   rewrite(adler_byte_sum(left, 0) == 0);
   rewrite(adler_byte_sum(right, 0) == 0);
   rewrite(adler_weighted_sum(left, 0, weight) == 0);
   rewrite(adler_weighted_sum(right, 0, weight) == 0);
   both { normalize(); } and { normalize(); }
  } else {
   have 0 < n;
   have 0 <= n - 1 by arithmetic() using { 0 < n; };
   have n - 1 < n by arithmetic() using { 0 < n; };
   have n - 1 <= bound by arithmetic() using { n <= bound; 0 < n; };
   have n - 1 < bound by arithmetic() using { n <= bound; 0 < n; };
   apply(ih(n - 1)) using {
    0 <= n - 1; n - 1 < n; n - 1 <= bound;
    forall (k: int32) { 0 <= k and k < bound implies left[k] == right[k] };
   }
   instantiate(forall (k: int32) { 0 <= k and k < bound implies left[k] == right[k] }, n - 1) using { 0 <= n - 1; n - 1 < bound; }
   apply(adler_sum_append(left, n)) using { 0 < n; }
   apply(adler_sum_append(right, n)) using { 0 < n; }
   apply(adler_weighted_append(left, n, weight)) using { 0 < n; }
   apply(adler_weighted_append(right, n, weight)) using { 0 < n; }
   both {
    rewrite(adler_byte_sum(left, n) == adler_byte_sum(left, n - 1) + to_integer((int32)left[n - 1]));
    rewrite(adler_byte_sum(right, n) == adler_byte_sum(right, n - 1) + to_integer((int32)right[n - 1]));
    rewrite(adler_byte_sum(left, n - 1) == adler_byte_sum(right, n - 1));
    rewrite(left[n - 1] == right[n - 1]);
    normalize();
   } and {
    rewrite(adler_weighted_sum(left, n, weight) == adler_weighted_sum(left, n - 1, weight) + (to_integer(weight) - to_integer(n - 1)) * to_integer((int32)left[n - 1]));
    rewrite(adler_weighted_sum(right, n, weight) == adler_weighted_sum(right, n - 1, weight) + (to_integer(weight) - to_integer(n - 1)) * to_integer((int32)right[n - 1]));
    rewrite(adler_weighted_sum(left, n - 1, weight) == adler_weighted_sum(right, n - 1, weight));
    rewrite(left[n - 1] == right[n - 1]);
    normalize();
   }
  }
 }
}

theorem adler_spec_extensional(left: uint8[], right: uint8[], length: int32, a0: Integer, b0: Integer) {
 requires 0 <= length;
 requires forall (k: int32) { 0 <= k and k < length implies left[k] == right[k] };
 ensures adler_spec_a(left, length, a0) == adler_spec_a(right, length, a0) and adler_spec_b(left, length, a0, b0) == adler_spec_b(right, length, a0, b0) by {
  apply(adler_sums_extensional(left, right, length, length, length)) using {
   0 <= length; length <= length;
   forall (k: int32) { 0 <= k and k < length implies left[k] == right[k] };
  }
  both {
   unfold(adler_spec_a(left, length, a0));
   unfold(adler_spec_a(right, length, a0));
   rewrite(adler_byte_sum(left, length) == adler_byte_sum(right, length));
   normalize();
  } and {
   unfold(adler_spec_b(left, length, a0, b0));
   unfold(adler_spec_b(right, length, a0, b0));
   rewrite(adler_weighted_sum(left, length, length) == adler_weighted_sum(right, length, length));
   normalize();
  }
 }
}
