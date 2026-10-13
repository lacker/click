# Pure observation of the source counter, not a generated program local.
import "../adler2/count-bridge.click";
import "../../adler32-spec.click";
function zlib_prefix_count(total: uint64, remaining: uint64) -> int32 {
 (int32)(uint32)(total - remaining)
}
theorem zlib_prefix_observation(total: uint64, remaining: uint64) {
 requires total - remaining <= 15u64;
 ensures to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining) by {
  have total - remaining <= 22208u64 by arithmetic() using { total - remaining <= 15u64; };
  apply(adler_count_observation(total - remaining));
  unfold(zlib_prefix_count(total, remaining));
  assumption();
 }
 ensures 0 <= zlib_prefix_count(total, remaining) and zlib_prefix_count(total, remaining) <= 22208 by {
  have total - remaining <= 22208u64 by arithmetic() using { total - remaining <= 15u64; };
  apply(adler_count_bounds(total - remaining));
  unfold(zlib_prefix_count(total, remaining));
  assumption();
 }
}
theorem zlib_prefix_pointer(base: const uint8*, total: uint64, remaining: uint64) {
 requires total - remaining <= 15u64;
 ensures base + (total - remaining) == base + zlib_prefix_count(total, remaining) by {
  have total - remaining <= 22208u64 by arithmetic() using { total - remaining <= 15u64; };
  apply(adler_count_byte_pointer(base, total - remaining));
  unfold(zlib_prefix_count(total, remaining));
  assumption();
 }
}

function zlib_byte_integer(value: uint8) -> Integer {
 to_integer((int32)value)
}
theorem zlib_byte_integer_identity(value: uint8) {
 ensures zlib_byte_integer(value) == to_integer((int32)value) by {
  unfold(zlib_byte_integer(value)); normalize();
 }
}
theorem zlib_prefix_append(bytes: uint8[], total: uint64, remaining: uint64) {
 requires 0 < zlib_prefix_count(total, remaining);
 ensures adler_byte_sum(bytes, zlib_prefix_count(total, remaining)) == adler_byte_sum(bytes, zlib_prefix_count(total, remaining) - 1) + zlib_byte_integer(bytes[zlib_prefix_count(total, remaining) - 1]) by {
  apply(adler_sum_append(bytes, zlib_prefix_count(total, remaining)));
  unfold(zlib_byte_integer(bytes[zlib_prefix_count(total, remaining) - 1]));
  assumption();
 }
}
theorem zlib_positive_count(value: int32) {
 requires 1 <= value;
 ensures 0 < value by { arithmetic() using { 1 <= value; } }
}
theorem zlib_equal_byte_integers(left: uint8, right: uint8) {
 requires (int32)left == (int32)right;
 ensures zlib_byte_integer(left) == zlib_byte_integer(right) by {
  unfold(zlib_byte_integer(left));
  unfold(zlib_byte_integer(right));
  rewrite((int32)left == (int32)right);
  normalize();
 }
}

# Packing after the original C short-path reduction, from exact component sums.
theorem zlib_short_result(bytes: uint8[], length: int32, a: uint64, b: uint64) {
 requires to_integer(a) == 1 + adler_byte_sum(bytes, length);
 requires to_integer(b) == to_integer(length) + adler_weighted_sum(bytes, length, length);
 requires 1 <= to_integer(a);
 requires to_integer(a) <= 3826;
 requires 0 <= to_integer(b);
 requires to_integer(b) <= 57390;
 ensures to_integer(a | ((b % 65521u64) << 16)) == adler_spec_checksum(bytes, length, 1, 0) by {
  have to_integer(a) <= 65520 by arithmetic() using { to_integer(a) <= 3826; };
  have 0 <= to_integer(a) by arithmetic() using { 1 <= to_integer(a); };
  have to_integer(a) == 0 * 65521 + to_integer(a) by arithmetic() using {};
  apply(adler_residue_unique(to_integer(a), 0, to_integer(a)));
  have adler_spec_a(bytes, length, 1) == to_integer(a) by {
   unfold(adler_spec_a(bytes, length, 1));
   rewrite(1 + adler_byte_sum(bytes, length) == to_integer(a));
   assumption();
  }
  apply(uint64_remainder_to_integer(b, 65521u64));
  apply(integer_positive_divisor_remainder_upper(to_integer(b), 65521));
  have to_integer(b % 65521u64) <= 65535 by arithmetic() using {
   to_integer(b % 65521u64) == truncating_remainder(to_integer(b), 65521);
   truncating_remainder(to_integer(b), 65521) <= 65521 - 1;
  };
  apply(uint64_to_integer_less_equal_implies_less_equal(b % 65521u64, 65535u64));
  have to_integer(a) <= 65535 by arithmetic() using { to_integer(a) <= 3826; };
  apply(uint64_to_integer_less_equal_implies_less_equal(a, 65535u64));
  apply(uint64_pack_uint16_to_integer(a, b % 65521u64));
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
   to_integer(a | ((b % 65521u64) << 16)) == to_integer(a) + 65536 * to_integer(b % 65521u64);
   adler_spec_a(bytes, length, 1) == to_integer(a);
   adler_spec_b(bytes, length, 1, 0) == to_integer(b % 65521u64);
  };
 }
}
