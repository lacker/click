import click::integer;
import click::machine_integer;

// Shared Adler-32 specification over a logical byte snapshot.
// Counts retain their native unsigned width; sums and weights use Integer arithmetic.
// These are mathematical lemmas; neither implementation's result is assumed.

function adler_byte_sum(bytes: uint8[], end: uint64) -> Integer {
 (0..end).fold(0, |acc, k| { acc + to_integer((int32)bytes[k]) })
}
function adler_weighted_sum(bytes: uint8[], end: uint64, weight_end: Integer) -> Integer {
 (0..end).fold(0, |acc, k| {
  acc + (weight_end - to_integer(k)) * to_integer((int32)bytes[k])
 })
}
function adler_spec_a(bytes: uint8[], length: uint64, a0: Integer) -> Integer {
 truncating_remainder(a0 + adler_byte_sum(bytes, length), 65521)
}
function adler_spec_b(bytes: uint8[], length: uint64, a0: Integer, b0: Integer) -> Integer {
 truncating_remainder(b0 + to_integer(length) * a0 + adler_weighted_sum(bytes, length, to_integer(length)), 65521)
}
theorem adler_sum_empty(bytes: uint8[], weight_end: Integer) {
 ensures adler_byte_sum(bytes, 0) == 0 by { peel(adler_byte_sum(bytes, 0)) using { 0 >= 0; }; simp(); }
 ensures adler_weighted_sum(bytes, 0, weight_end) == 0 by { peel(adler_weighted_sum(bytes, 0, weight_end)) using { 0 >= 0; }; simp(); }
}

theorem adler_sum_append(bytes: uint8[], n: uint64) {
 requires 0 < n;
 ensures adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]) by {
  have 0 <= n - 1 by { arithmetic() using { 0 < n; }; }
  have n - 1 < 18446744073709551615u64 by { arithmetic() using { 0 < n; }; }
  peel(adler_byte_sum(bytes, n)) using { 0 <= n - 1; n - 1 < 18446744073709551615u64; };
  normalize();
 }
}
theorem adler_weighted_append(bytes: uint8[], n: uint64, weight_end: Integer) {
 requires 0 < n;
 ensures adler_weighted_sum(bytes, n, weight_end) == adler_weighted_sum(bytes, n - 1, weight_end) + (weight_end - to_integer(n - 1)) * to_integer((int32)bytes[n - 1]) by {
  have 0 <= n - 1 by { arithmetic() using { 0 < n; }; }
  have n - 1 < 18446744073709551615u64 by { arithmetic() using { 0 < n; }; }
  peel(adler_weighted_sum(bytes, n, weight_end)) using { 0 <= n - 1; n - 1 < 18446744073709551615u64; };
  normalize();
 }
}

theorem adler_weight_shift(bytes: uint8[], n: uint64, w0: Integer, w1: Integer) {
 requires 0 <= n;
 ensures adler_weighted_sum(bytes, n, w1) - adler_weighted_sum(bytes, n, w0) == (w1 - w0) * adler_byte_sum(bytes, n) by {
  induct(n) as ih;
  if n <= 0 {
   peel(adler_weighted_sum(bytes, n, w1)) using { n <= 0; };
   peel(adler_weighted_sum(bytes, n, w0)) using { n <= 0; };
   peel(adler_byte_sum(bytes, n)) using { n <= 0; };
   have adler_weighted_sum(bytes, n, w1) == 0 by { assumption(); }
   have adler_weighted_sum(bytes, n, w0) == 0 by { assumption(); }
   have adler_byte_sum(bytes, n) == 0 by { assumption(); }
   arithmetic() using { adler_weighted_sum(bytes, n, w1) == 0; adler_weighted_sum(bytes, n, w0) == 0; adler_byte_sum(bytes, n) == 0; };
  } else {
   have 0 < n by { simp(); }
   have 0 <= n - 1 by { arithmetic() using { 0 < n; }; }
   have n - 1 < n by { arithmetic() using { 0 < n; }; }
   have n - 1 < 18446744073709551615u64 by { arithmetic() using { 0 < n; }; }
   apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; };
   peel(adler_weighted_sum(bytes, n, w1)) using { 0 <= n - 1; n - 1 < 18446744073709551615u64; };
   peel(adler_weighted_sum(bytes, n, w0)) using { 0 <= n - 1; n - 1 < 18446744073709551615u64; };
   peel(adler_byte_sum(bytes, n)) using { 0 <= n - 1; n - 1 < 18446744073709551615u64; };
   have (adler_weighted_sum(bytes, n - 1, w1) + (w1 - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) - (adler_weighted_sum(bytes, n - 1, w0) + (w0 - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) == (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (w1 - w0) * to_integer((int32)bytes[n - 1]) by {
    arithmetic_certificate rules {
     integer_polynomial_identity bounds [] => (adler_weighted_sum(bytes, n - 1, w1) + (w1 - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) - (adler_weighted_sum(bytes, n - 1, w0) + (w0 - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) == (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (w1 - w0) * to_integer((int32)bytes[n - 1]);
     conclusion 0;
    }
   }
   rewrite((adler_weighted_sum(bytes, n - 1, w1) + (w1 - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) - (adler_weighted_sum(bytes, n - 1, w0) + (w0 - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) == (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (w1 - w0) * to_integer((int32)bytes[n - 1]));
   rewrite(adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0) == (w1 - w0) * adler_byte_sum(bytes, n - 1));
   arithmetic_certificate rules {
    integer_polynomial_identity bounds [] => (w1 - w0) * adler_byte_sum(bytes, n - 1) + (w1 - w0) * to_integer((int32)bytes[n - 1]) == (w1 - w0) * (adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]));
    conclusion 0;
   }
  }
 }
}

theorem adler_weighted_prefix_step(bytes: uint8[], n: uint64) {
 requires 0 < n;
 ensures adler_weighted_sum(bytes, n, to_integer(n)) == adler_weighted_sum(bytes, n - 1, to_integer(n - 1)) + adler_byte_sum(bytes, n) by {
  have 0 <= n - 1 by { arithmetic() using { 0 < n; }; }
  have defined(n - 1) by { simp() using { 0 < n; }; }
  have 1u64 <= n by arithmetic() using { 0 < n; };
  apply(uint64_less_equal_to_integer(1u64, n)) using { 1u64 <= n; };
  apply(uint64_subtract_to_integer(n, 1u64)) using { to_integer(1u64) <= to_integer(n); };
  have to_integer(n) - to_integer(n - 1) == 1 by { arithmetic() using { to_integer(n - 1) == to_integer(n) - to_integer(1); }; }
  apply(adler_weight_shift(bytes, n - 1, to_integer(n - 1), to_integer(n))) using { 0 <= n - 1; };
  have adler_byte_sum(bytes, n - 1) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1) by {
   rewrite(to_integer(n) - to_integer(n - 1) == 1);
   arithmetic() using { };
  }
  have adler_weighted_sum(bytes, n - 1, to_integer(n)) == adler_weighted_sum(bytes, n - 1, to_integer(n - 1)) + adler_byte_sum(bytes, n - 1) by {
   rewrite(adler_byte_sum(bytes, n - 1) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1));
   arithmetic() using { adler_weighted_sum(bytes, n - 1, to_integer(n)) - adler_weighted_sum(bytes, n - 1, to_integer(n - 1)) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1); to_integer(n) - to_integer(n - 1) == 1; };
  }
  apply(adler_weighted_append(bytes, n, to_integer(n))) using { 0 < n; };
  apply(adler_sum_append(bytes, n)) using { 0 < n; };
  rewrite(adler_weighted_sum(bytes, n, to_integer(n)) == adler_weighted_sum(bytes, n - 1, to_integer(n)) + (to_integer(n) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1]));
  rewrite(adler_weighted_sum(bytes, n - 1, to_integer(n)) == adler_weighted_sum(bytes, n - 1, to_integer(n - 1)) + adler_byte_sum(bytes, n - 1));
  rewrite(to_integer(n) - to_integer(n - 1) == 1);
  rewrite(adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]));
  arithmetic() using { };
 }
}

theorem adler_byte_bounds(value: uint8) {
 ensures 0 <= to_integer((int32)value) by {
  have 0 <= (int32)value by { simp(); }
  apply(int32_less_equal_to_integer(0, (int32)value)) using { 0 <= (int32)value; };
  assumption();
 }
 ensures to_integer((int32)value) <= 255 by {
  have (int32)value <= 255 by { simp(); }
  apply(int32_less_equal_to_integer((int32)value, 255)) using { (int32)value <= 255; };
  assumption();
 }
}


theorem adler_sum_nonnegative(bytes: uint8[], n: uint64) {
 requires 0 <= n;
 ensures 0 <= adler_byte_sum(bytes, n) by {
  induct(n) as ih;
  if n <= 0 {
   peel(adler_byte_sum(bytes, n)) using { n <= 0; };
   arithmetic() using { adler_byte_sum(bytes, n) == 0; };
  } else {
   have 0 < n by { simp(); }
   have 0 <= n - 1 by { arithmetic() using { 0 < n; }; }
   have n - 1 < n by { arithmetic() using { 0 < n; }; }
   apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; };
   apply(adler_byte_bounds(bytes[n - 1]));
   apply(adler_sum_append(bytes, n)) using { 0 < n; };
   rewrite(adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]));
   arithmetic() using { 0 <= adler_byte_sum(bytes, n - 1); 0 <= to_integer((int32)bytes[n - 1]); };
  }
 }
}
theorem adler_weighted_nonnegative(bytes: uint8[], n: uint64) {
 requires 0 <= n;
 ensures 0 <= adler_weighted_sum(bytes, n, to_integer(n)) by {
  induct(n) as ih;
  if n <= 0 {
   peel(adler_weighted_sum(bytes, n, to_integer(n))) using { n <= 0; };
   arithmetic() using { adler_weighted_sum(bytes, n, to_integer(n)) == 0; };
  } else {
   have 0 < n by { simp(); }
   have 0 <= n - 1 by { arithmetic() using { 0 < n; }; }
   have n - 1 < n by { arithmetic() using { 0 < n; }; }
   apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; };
   apply(adler_sum_nonnegative(bytes, n)) using { 0 <= n; };
   apply(adler_weighted_prefix_step(bytes, n)) using { 0 < n; };
   rewrite(adler_weighted_sum(bytes, n, to_integer(n)) == adler_weighted_sum(bytes, n - 1, to_integer(n - 1)) + adler_byte_sum(bytes, n));
   arithmetic() using { 0 <= adler_weighted_sum(bytes, n - 1, to_integer(n - 1)); 0 <= adler_byte_sum(bytes, n); };
  }
 }
}
