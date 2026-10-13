import "short-prefix.click";
import "byte.click";

// One mathematical scalar recurrence, reused for each unchanged DO16 lane.
theorem zlib_component_step(bytes: uint8[], n: int32) {
 requires 0 <= n;
 requires n < 2147483647;
 ensures adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + zlib_byte_integer(bytes[n]) by {
  have 0 < n + 1 by arithmetic() using { 0 <= n; n < 2147483647; };
  apply(adler_sum_append(bytes, n + 1));
  have n + 1 - 1 == n by arithmetic() using { 0 <= n; n < 2147483647; };
  unfold(zlib_byte_integer(bytes[n]));
  normalize() using { adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n + 1 - 1) + to_integer((int32)bytes[n + 1 - 1]); n + 1 - 1 == n; };
 }
 ensures adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n + 1) by {
  have 0 < n + 1 by arithmetic() using { 0 <= n; n < 2147483647; };
  apply(adler_weighted_prefix_step(bytes, n + 1));
  have n + 1 - 1 == n by arithmetic() using { 0 <= n; n < 2147483647; };
  normalize() using { adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n + 1 - 1, n + 1 - 1) + adler_byte_sum(bytes, n + 1); n + 1 - 1 == n; };
 }
}

theorem zlib_reduced_result(bytes: uint8[], length: int32, a: uint64, b: uint64) {
 requires to_integer(a) == 1 + adler_byte_sum(bytes, length);
 requires to_integer(b) == to_integer(length) + adler_weighted_sum(bytes, length, length);
 ensures to_integer((a % 65521u64) | ((b % 65521u64) << 16)) == adler_spec_checksum(bytes, length, 1, 0) by {
  apply(uint64_remainder_to_integer(a, 65521u64));
  apply(uint64_remainder_to_integer(b, 65521u64));
  apply(integer_positive_divisor_remainder_upper(to_integer(a), 65521));
  apply(integer_positive_divisor_remainder_upper(to_integer(b), 65521));
  have to_integer(a % 65521u64) <= 65535 by arithmetic() using {
   to_integer(a % 65521u64) == truncating_remainder(to_integer(a), 65521);
   truncating_remainder(to_integer(a), 65521) <= 65521 - 1;
  };
  have to_integer(b % 65521u64) <= 65535 by arithmetic() using {
   to_integer(b % 65521u64) == truncating_remainder(to_integer(b), 65521);
   truncating_remainder(to_integer(b), 65521) <= 65521 - 1;
  };
  apply(uint64_to_integer_less_equal_implies_less_equal(a % 65521u64, 65535u64));
  apply(uint64_to_integer_less_equal_implies_less_equal(b % 65521u64, 65535u64));
  apply(uint64_pack_uint16_to_integer(a % 65521u64, b % 65521u64));
  have adler_spec_a(bytes, length, 1) == to_integer(a % 65521u64) by {
   unfold(adler_spec_a(bytes, length, 1));
   rewrite(1 + adler_byte_sum(bytes, length) == to_integer(a));
   simp() using { to_integer(a % 65521u64) == truncating_remainder(to_integer(a), 65521); };
  }
  have adler_spec_b(bytes, length, 1, 0) == to_integer(b % 65521u64) by {
   unfold(adler_spec_b(bytes, length, 1, 0));
   have 0 + to_integer(length) * 1 + adler_weighted_sum(bytes, length, length) == to_integer(b) by arithmetic() using {
    to_integer(b) == to_integer(length) + adler_weighted_sum(bytes, length, length);
   };
   rewrite(0 + to_integer(length) * 1 + adler_weighted_sum(bytes, length, length) == to_integer(b));
   simp() using { to_integer(b % 65521u64) == truncating_remainder(to_integer(b), 65521); };
  }
  unfold(adler_spec_checksum(bytes, length, 1, 0));
  arithmetic() using {
   to_integer((a % 65521u64) | ((b % 65521u64) << 16)) == to_integer(a % 65521u64) + 65536 * to_integer(b % 65521u64);
   adler_spec_a(bytes, length, 1) == to_integer(a % 65521u64);
   adler_spec_b(bytes, length, 1, 0) == to_integer(b % 65521u64);
  };
 }
}

// A checked native recurrence for one original C addition pair within a batch.
// The byte equality is over C's promoted value; neither memory nor a callee
// checksum summary is assumed by this lemma.
theorem zlib_native_component_step(bytes: uint8[], n: int32, a: uint64, b: uint64, value: uint8) {
 requires 0 <= n;
 requires n < 5552;
 requires (int32)value == (int32)bytes[n];
 requires to_integer(a) == 1 + adler_byte_sum(bytes, n);
 requires to_integer(b) == to_integer(n) + adler_weighted_sum(bytes, n, n);
 requires to_integer(a) <= 1 + 255 * to_integer(n);
 requires to_integer(b) <= 1415761 * to_integer(n);
 ensures to_integer(a + (uint64)(uint32)value) == 1 + adler_byte_sum(bytes, n + 1)
     and to_integer(b + (a + (uint64)(uint32)value)) == to_integer(n + 1) + adler_weighted_sum(bytes, n + 1, n + 1)
     and to_integer(a + (uint64)(uint32)value) <= 1 + 255 * to_integer(n + 1)
     and to_integer(b + (a + (uint64)(uint32)value)) <= 1415761 * to_integer(n + 1) by {
  have n <= 5551 by arithmetic() using { n < 5552; };
  have n < 2147483647 by arithmetic() using { n < 5552; };
  apply(int32_less_equal_to_integer(n, 5551));
  have defined(n + 1) by simp();
  apply(int32_add_to_integer(n, 1));
  apply(zlib_byte_u64(value));
  apply(zlib_byte_integer_identity(value));
  apply(zlib_equal_byte_integers(value, bytes[n]));
  apply(zlib_component_step(bytes, n));
  have to_integer(a) + to_integer((uint64)(uint32)value) <= 1415761 by arithmetic() using {
   to_integer(a) <= 1 + 255 * to_integer(n);
   to_integer(n) <= 5551;
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   to_integer((int32)value) <= 255;
  };
  have to_integer(a) + to_integer((uint64)(uint32)value) <= 18446744073709551615 by arithmetic() using { to_integer(a) + to_integer((uint64)(uint32)value) <= 1415761; };
  apply(uint64_add_to_integer(a, (uint64)(uint32)value));
  have to_integer(a + (uint64)(uint32)value) <= 1415761 by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) + to_integer((uint64)(uint32)value) <= 1415761;
  };
  have to_integer(b) + to_integer(a + (uint64)(uint32)value) <= 18446744073709551615 by arithmetic() using {
   to_integer(b) <= 1415761 * to_integer(n);
   to_integer(n) <= 5551;
   to_integer(a + (uint64)(uint32)value) <= 1415761;
  };
  apply(uint64_add_to_integer(b, a + (uint64)(uint32)value));
  have to_integer(a + (uint64)(uint32)value) == 1 + adler_byte_sum(bytes, n + 1) by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) == 1 + adler_byte_sum(bytes, n);
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   zlib_byte_integer(value) == to_integer((int32)value);
   zlib_byte_integer(value) == zlib_byte_integer(bytes[n]);
   adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + zlib_byte_integer(bytes[n]);
  };
  have to_integer(b + (a + (uint64)(uint32)value)) == to_integer(n + 1) + adler_weighted_sum(bytes, n + 1, n + 1) by arithmetic() using {
   to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b) + to_integer(a + (uint64)(uint32)value);
   to_integer(b) == to_integer(n) + adler_weighted_sum(bytes, n, n);
   to_integer(a + (uint64)(uint32)value) == 1 + adler_byte_sum(bytes, n + 1);
   adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n + 1);
   to_integer(n + 1) == to_integer(n) + to_integer(1);
  };
  have to_integer(a + (uint64)(uint32)value) <= 1 + 255 * to_integer(n + 1) by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) <= 1 + 255 * to_integer(n);
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   to_integer((int32)value) <= 255;
   to_integer(n + 1) == to_integer(n) + to_integer(1);
  };
  have to_integer(b + (a + (uint64)(uint32)value)) <= 1415761 * to_integer(n + 1) by arithmetic() using {
   to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b) + to_integer(a + (uint64)(uint32)value);
   to_integer(b) <= 1415761 * to_integer(n);
   to_integer(a + (uint64)(uint32)value) <= 1415761;
   to_integer(n + 1) == to_integer(n) + to_integer(1);
  };
  simp();
 }
}
