# The 32-bit view of a 64-bit iterator count.
# A chunk iterator counts its remaining bytes as `usize`. The lane and tail
# bound libraries state their ceilings over an `int32` count; within one
# batch the count is at most 22208, where the view `(int32)(uint32)count`
# is the count itself. These carry the iterator's 64-bit facts to that view.

theorem adler_count_observation(r: uint64) {
 requires r <= 22208u64;
 ensures to_integer((int32)(uint32)r) == to_integer(r) by {
  have 0u64 <= r by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, r)) using { 0u64 <= r; }
  apply(uint64_less_equal_to_integer(r, 22208u64)) using { r <= 22208u64; }
  arithmetic_certificate special {
   premise 0: 0 <= to_integer(r) => 0 <= to_integer(r);
   premise 1: to_integer(r) <= 22208 => to_integer(r) <= 22208;
   integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)r) == to_integer(r);
   conclusion 0;
  }
 }
}
theorem adler_count_bounds(r: uint64) {
 requires r <= 22208u64;
 ensures 0 <= (int32)(uint32)r and (int32)(uint32)r <= 22208 by {
  apply(adler_count_observation(r)) using { r <= 22208u64; }
  have 0u64 <= r by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, r)) using { 0u64 <= r; }
  apply(uint64_less_equal_to_integer(r, 22208u64)) using { r <= 22208u64; }
  have 0 <= to_integer((int32)(uint32)r) by { rewrite(to_integer((int32)(uint32)r) == to_integer(r)); assumption(); }
  have to_integer((int32)(uint32)r) <= 22208 by { rewrite(to_integer((int32)(uint32)r) == to_integer(r)); assumption(); }
  both {
   apply(int32_less_equal_of_to_integer(0, (int32)(uint32)r)) using { 0 <= to_integer((int32)(uint32)r); }
  } and {
   apply(int32_less_equal_of_to_integer((int32)(uint32)r, 22208)) using { to_integer((int32)(uint32)r) <= 22208; }
  }
 }
}
theorem adler_count_at_least(r: uint64, k: uint64) {
 requires k <= r;
 requires r <= 22208u64;
 ensures (int32)(uint32)k <= (int32)(uint32)r by {
  have k <= 22208u64 by { arithmetic() using { k <= r; r <= 22208u64; } }
  apply(adler_count_observation(r)) using { r <= 22208u64; }
  apply(adler_count_observation(k)) using { k <= 22208u64; }
  apply(uint64_less_equal_to_integer(k, r)) using { k <= r; }
  have to_integer((int32)(uint32)k) <= to_integer((int32)(uint32)r) by {
   rewrite(to_integer((int32)(uint32)k) == to_integer(k));
   rewrite(to_integer((int32)(uint32)r) == to_integer(r));
   assumption();
  }
  apply(int32_less_equal_of_to_integer((int32)(uint32)k, (int32)(uint32)r)) using { to_integer((int32)(uint32)k) <= to_integer((int32)(uint32)r); }
 }
}
theorem adler_count_step(r: uint64, k: uint64) {
 requires k <= r;
 requires r <= 22208u64;
 ensures (int32)(uint32)(r - k) == (int32)(uint32)r - (int32)(uint32)k by {
  have k <= 22208u64 by { arithmetic() using { k <= r; r <= 22208u64; } }
  have r - k <= 22208u64 by { arithmetic() using { k <= r; r <= 22208u64; } }
  apply(adler_count_observation(r)) using { r <= 22208u64; }
  apply(adler_count_observation(k)) using { k <= 22208u64; }
  apply(adler_count_observation(r - k)) using { r - k <= 22208u64; }
  apply(adler_count_bounds(r)) using { r <= 22208u64; }
  apply(adler_count_bounds(k)) using { k <= 22208u64; }
  apply(adler_count_at_least(r, k)) using { k <= r; r <= 22208u64; }
  apply(uint64_less_equal_to_integer(k, r)) using { k <= r; }
  apply(uint64_subtract_to_integer(r, k)) using { to_integer(k) <= to_integer(r); }
  apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)r, (int32)(uint32)k)) using { 0 <= (int32)(uint32)k; (int32)(uint32)k <= (int32)(uint32)r; }
  apply(int32_subtract_to_integer((int32)(uint32)r, (int32)(uint32)k)) using { defined((int32)(uint32)r - (int32)(uint32)k); }
  have to_integer((int32)(uint32)(r - k)) == to_integer((int32)(uint32)r - (int32)(uint32)k) by {
   rewrite(to_integer((int32)(uint32)(r - k)) == to_integer(r - k));
   rewrite(to_integer(r - k) == to_integer(r) - to_integer(k));
   rewrite(to_integer((int32)(uint32)r - (int32)(uint32)k) == to_integer((int32)(uint32)r) - to_integer((int32)(uint32)k));
   rewrite(to_integer((int32)(uint32)r) == to_integer(r));
   rewrite(to_integer((int32)(uint32)k) == to_integer(k));
   normalize();
  }
  apply(int32_equal_of_to_integer((int32)(uint32)(r - k), (int32)(uint32)r - (int32)(uint32)k)) using { to_integer((int32)(uint32)(r - k)) == to_integer((int32)(uint32)r - (int32)(uint32)k); }
 }
}
theorem adler_count_lane_step(r: uint64) {
 requires 4u64 <= r;
 requires r <= 22208u64;
 ensures 4 <= (int32)(uint32)r by {
  apply(adler_count_at_least(r, 4u64)) using { 4u64 <= r; r <= 22208u64; }
  normalize() using { (int32)(uint32)4u64 <= (int32)(uint32)r; }
 }
 ensures (int32)(uint32)(r - 4u64) == (int32)(uint32)r - 4 by {
  apply(adler_count_step(r, 4u64)) using { 4u64 <= r; r <= 22208u64; }
  normalize() using { (int32)(uint32)(r - 4u64) == (int32)(uint32)r - (int32)(uint32)4u64; }
 }
}
theorem adler_count_tail_step(r: uint64) {
 requires 1u64 <= r;
 requires r <= 22208u64;
 ensures 1 <= (int32)(uint32)r by {
  apply(adler_count_at_least(r, 1u64)) using { 1u64 <= r; r <= 22208u64; }
  normalize() using { (int32)(uint32)1u64 <= (int32)(uint32)r; }
 }
 ensures (int32)(uint32)(r - 1u64) == (int32)(uint32)r - 1 by {
  apply(adler_count_step(r, 1u64)) using { 1u64 <= r; r <= 22208u64; }
  normalize() using { (int32)(uint32)(r - 1u64) == (int32)(uint32)r - (int32)(uint32)1u64; }
 }
}
theorem adler_count_zero(r: uint64) {
 requires r <= 22208u64;
 requires (int32)(uint32)r == 0;
 ensures r == 0u64 by {
  apply(adler_count_observation(r)) using { r <= 22208u64; }
  have to_integer((int32)(uint32)r) == 0 by { rewrite((int32)(uint32)r == 0); normalize(); }
  have to_integer(r) == 0 by { arithmetic() using { to_integer((int32)(uint32)r) == to_integer(r); to_integer((int32)(uint32)r) == 0; } }
  have to_integer(r) == to_integer(0u64) by { normalize() using { to_integer(r) == 0; } }
  apply(uint64_equal_of_to_integer(r, 0u64)) using { to_integer(r) == to_integer(0u64); }
 }
}

# Within the checked small-count range, the native cursor and the signed
# specification index denote exactly the same byte address.
theorem adler_count_byte_pointer(base: const uint8*, count: uint64) {
 requires count <= 22208u64;
 ensures base + count == base + (int32)(uint32)count by {
  apply(adler_count_observation(count)) using { count <= 22208u64; }
  normalize() using { to_integer((int32)(uint32)count) == to_integer(count); }
 }
}

# Read equality first, then transport the native byte into the Integer spec.
theorem adler_count_byte_observation(bytes: uint8[], count: uint64) {
 requires count <= 22208u64;
 ensures to_integer((int32)bytes[count]) == to_integer((int32)bytes[(int32)(uint32)count]) by {
  apply(adler_count_byte_pointer(bytes, count)) using { count <= 22208u64; }
  have bytes[count] == bytes[(int32)(uint32)count] by {
   simp() using { bytes + count == bytes + (int32)(uint32)count; }
  }
  rewrite(bytes[count] == bytes[(int32)(uint32)count]);
  normalize();
 }
}
theorem adler_count_chunk_byte_observation(bytes: uint8[], count: uint64, lane: int32) {
 requires count <= 22204u64;
 requires 0 <= lane;
 requires lane <= 3;
 ensures to_integer((int32)(bytes + count)[lane]) == to_integer((int32)bytes[(int32)(uint32)count + lane]) by {
  have count <= 22208u64 by { normalize() using { count <= 22204u64; } }
  apply(adler_count_byte_pointer(bytes, count)) using { count <= 22208u64; }
  apply(adler_count_bounds(count)) using { count <= 22208u64; }
  have (int32)(uint32)count <= 22204 by { simp(); }
  have defined((int32)(uint32)count + lane) by { simp(); }
  have bytes + count + lane == bytes + ((int32)(uint32)count + lane) by {
   rewrite(bytes + count == bytes + (int32)(uint32)count);
   normalize() using { defined((int32)(uint32)count + lane); }
  }
  have (bytes + count)[lane] == bytes[(int32)(uint32)count + lane] by {
   simp() using { bytes + count + lane == bytes + ((int32)(uint32)count + lane); }
  }
  rewrite((bytes + count)[lane] == bytes[(int32)(uint32)count + lane]);
  normalize();
 }
}

# After Next has consumed four bytes, recover their positions from the actual
# remaining count. No auxiliary processed count supplies the input position.
theorem adler_count_previous_chunk_byte_observation(bytes: uint8[], total: uint64, remaining: uint64, lane: int32) {
 requires remaining <= total;
 requires 4u64 <= total - remaining;
 requires total <= 22204u64;
 requires 0 <= (int32)(uint32)remaining;
 requires (int32)(uint32)remaining <= (int32)(uint32)total;
 requires (int32)(uint32)total <= 22204;
 requires 0 <= lane;
 requires lane <= 3;
 ensures to_integer((int32)(bytes + (total - remaining - 4u64))[lane]) == to_integer((int32)bytes[((int32)(uint32)total - (int32)(uint32)remaining) - 4 + lane]) by {
  have total <= 22208u64 by { normalize() using { total <= 22204u64; } }
  have total - remaining <= 22208u64 by { arithmetic() using { remaining <= total; total <= 22204u64; } }
  have total - remaining - 4u64 <= 22204u64 by { arithmetic() using { remaining <= total; 4u64 <= total - remaining; total <= 22204u64; } }
  apply(adler_count_step(total, remaining)) using { remaining <= total; total <= 22208u64; }
  apply(adler_count_lane_step(total - remaining)) using { 4u64 <= total - remaining; total - remaining <= 22208u64; }
  apply(adler_count_chunk_byte_observation(bytes, total - remaining - 4u64, lane)) using { total - remaining - 4u64 <= 22204u64; 0 <= lane; lane <= 3; }
  have (int32)(uint32)(total - remaining - 4u64) == ((int32)(uint32)total - (int32)(uint32)remaining) - 4 by {
   rewrite((int32)(uint32)(total - remaining - 4u64) == (int32)(uint32)(total - remaining) - 4);
   rewrite((int32)(uint32)(total - remaining) == (int32)(uint32)total - (int32)(uint32)remaining);
   normalize();
  }
  have ((int32)(uint32)total - (int32)(uint32)remaining) - 4 == (int32)(uint32)(total - remaining - 4u64) by { normalize() using { (int32)(uint32)(total - remaining - 4u64) == ((int32)(uint32)total - (int32)(uint32)remaining) - 4; } }
  rewrite(((int32)(uint32)total - (int32)(uint32)remaining) - 4 == (int32)(uint32)(total - remaining - 4u64));
  assumption();
 }
}

# Exact prefix advance used by the deferred scalar B contribution.
theorem adler_small_prefix_integer_advance(total: int32, remaining: int32) {
 requires 0 <= remaining;
 requires remaining <= total;
 requires total <= 22204;
 requires 4 <= total - remaining;
 ensures to_integer(total - remaining) == to_integer((total - remaining) - 4) + 4 by {
  apply(int32_nonnegative_subtract_within_value_is_defined(total, remaining)) using { 0 <= remaining; remaining <= total; };
  have defined(total - remaining) by { assumption(); }
  apply(int32_nonnegative_subtract_within_value_is_defined(total - remaining, 4)) using { 0 <= 4; 4 <= total - remaining; };
  have defined((total - remaining) - 4) by { simp(); }
  apply(int32_subtract_to_integer(total - remaining, 4)) using { defined((total - remaining) - 4); };
  arithmetic() using { to_integer((total - remaining) - 4) == to_integer(total - remaining) - to_integer(4); };
 }
}

# Recover the scalar byte from the actual post-Next remaining count.
theorem adler_count_previous_byte_observation(bytes: uint8[], total: uint64, remaining: uint64) {
 requires remaining <= total;
 requires 1u64 <= total - remaining;
 requires total <= 22207u64;
 requires 0 <= (int32)(uint32)remaining;
 requires (int32)(uint32)remaining <= (int32)(uint32)total;
 requires (int32)(uint32)total <= 22207;
 ensures to_integer((int32)(bytes + (total - remaining - 1u64))[0]) == to_integer((int32)bytes[((int32)(uint32)total - (int32)(uint32)remaining) - 1]) by {
  have total <= 22208u64 by { normalize() using { total <= 22207u64; } }
  have total - remaining <= 22208u64 by { arithmetic() using { remaining <= total; total <= 22207u64; } }
  have total - remaining - 1u64 <= 22207u64 by { arithmetic() using { remaining <= total; 1u64 <= total - remaining; total <= 22207u64; } }
  apply(adler_count_step(total, remaining)) using { remaining <= total; total <= 22208u64; }
  apply(adler_count_tail_step(total - remaining)) using { 1u64 <= total - remaining; total - remaining <= 22208u64; }
  have total - remaining - 1u64 <= 22208u64 by { normalize() using { total - remaining - 1u64 <= 22207u64; } }
  apply(adler_count_byte_observation(bytes, total - remaining - 1u64)) using { total - remaining - 1u64 <= 22208u64; }
  have (int32)(uint32)(total - remaining - 1u64) == ((int32)(uint32)total - (int32)(uint32)remaining) - 1 by {
   rewrite((int32)(uint32)(total - remaining - 1u64) == (int32)(uint32)(total - remaining) - 1);
   rewrite((int32)(uint32)(total - remaining) == (int32)(uint32)total - (int32)(uint32)remaining);
   normalize();
  }
  have ((int32)(uint32)total - (int32)(uint32)remaining) - 1 == (int32)(uint32)(total - remaining - 1u64) by { normalize() using { (int32)(uint32)(total - remaining - 1u64) == ((int32)(uint32)total - (int32)(uint32)remaining) - 1; } }
  rewrite(((int32)(uint32)total - (int32)(uint32)remaining) - 1 == (int32)(uint32)(total - remaining - 1u64));
  normalize() using { to_integer((int32)bytes[total - remaining - 1u64]) == to_integer((int32)bytes[(int32)(uint32)(total - remaining - 1u64)]); }
 }
}
