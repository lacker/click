import click::integer;

// Whole-body checksum correctness, bounds and termination for unchanged Adler32::compute.
// Canonical seeds and every slice length: positions are uint64 cursors and no
// length bound is required.
// The harness checks the helper bodies and assembles their arithmetic libraries.
// Every loop carries both lane residues against the uint64 specification at its
// actual iterator cursor; batch-local counts stay int32 (at most 22208).
// Vector and scalar steps read input bytes at the uint64 cursor and apply the
// int32 step at offset 0 of the input there (the _u64 step lemmas below).
// Original remainder reductions and recombination preserve both residues.
// The original scalar tail and final fields satisfy the common entry-input specification.

theorem adler_uint64_self_subtract(n: uint64) { ensures to_integer(n - n) == to_integer(0u64) by normalize(); }
theorem adler_i32_below_mod(n: int32) { requires n <= 65520; ensures n < 65521 by solve() using { n <= 65520; }; }
theorem adler_bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22204;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by solve() using { 0 <= index; index <= 22204; };
  normalize() using { defined(index + 4); };
 }
}
theorem adler_scalar_batch_product_bound(length: uint32, seed: uint32) {
 requires length <= 22204u32;
 requires seed <= 65520u32;
 ensures to_integer(length) * to_integer(seed) <= 1454806080 by {
  have 0 <= to_integer(length);
  have to_integer(length) <= 4294967295;
  have 0 <= to_integer(seed);
  have to_integer(seed) <= 4294967295;
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(length) => 0 <= to_integer(length);
   premise 1: to_integer(length) <= 22204 => to_integer(length) <= 22204;
   premise 2: 0 <= to_integer(seed) => 0 <= to_integer(seed);
   premise 3: to_integer(seed) <= 65520 => to_integer(seed) <= 65520;
   integer_product_bounds bounds [0, 1, 2, 3] => to_integer(length) * to_integer(seed) <= 1454806080;
   conclusion 0;
  }
 }
}
theorem adler_small_length_cast(length: uint64) {
 requires length <= 22204u64;
 ensures (length as u32) <= 22204u32 by {
  have 0u64 <= length by normalize();
  have 0 <= to_integer(length) by known();
  have to_integer(length) <= 4294967295 by solve() using { to_integer(length) <= 22204; };
  have to_integer((length as u32)) == to_integer(length) by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer(length) => 0 <= to_integer(length);
    premise 1: to_integer(length) <= 4294967295 => to_integer(length) <= 4294967295;
    integer_cast_identity bounds [0, 1] => to_integer((length as u32)) == to_integer(length);
    conclusion 0;
   }
  }
  have to_integer((length as u32)) <= to_integer(22204u32) by { rewrite(to_integer((length as u32)), to_integer(length)); known(); }
  known();
 }
}



theorem adler_tail_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 2147483646;
 ensures (base + index) + 1 == base + (index + 1) by {
  have defined(index + 1) by solve() using { 0 <= index; index <= 2147483646; };
  normalize() using { defined(index + 1); };
 }
}

// Full-width positions for the unchanged vector and scalar steps: each step
// is the int32 step at offset 0 of the input suffix at the uint64 position,
// bridged at its constant width and concatenated to the uint64 prefix.
theorem adler_native_four_lane_a_prefix_step_u64(bytes: uint8[], n: uint64, a_seed: Integer, a: Integer, a0: uint32, a1: uint32, a2: uint32, a3: uint32, v0: uint32, v1: uint32, v2: uint32, v3: uint32) {
 requires to_integer(n) + 4 <= 18446744073709551615;
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= a;
 requires truncating_remainder(adler_lane_a(a, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a_u64(bytes, n, a_seed);
 requires to_integer(v0) == to_integer((bytes + n)[0] as int32);
 requires to_integer(a0) + to_integer(v0) <= 4294967295;
 requires to_integer(v1) == to_integer((bytes + n)[1] as int32);
 requires to_integer(a1) + to_integer(v1) <= 4294967295;
 requires to_integer(v2) == to_integer((bytes + n)[2] as int32);
 requires to_integer(a2) + to_integer(v2) <= 4294967295;
 requires to_integer(v3) == to_integer((bytes + n)[3] as int32);
 requires to_integer(a3) + to_integer(v3) <= 4294967295;
 ensures truncating_remainder(adler_lane_a(a, to_integer((a0 + v0)), to_integer((a1 + v1)), to_integer((a2 + v2)), to_integer((a3 + v3))), 65521) == adler_spec_a_u64(bytes, n + 4u64, a_seed) by {
  apply(adler_spec_a_canonical_u64(bytes, n, a_seed)) using { 0 <= a_seed; };
  apply(adler_spec_empty(bytes + n, adler_spec_a_u64(bytes, n, a_seed), 0)) using { 0 <= adler_spec_a_u64(bytes, n, a_seed); adler_spec_a_u64(bytes, n, a_seed) <= 65520; 0 <= 0; 0 <= 65520; };
  have truncating_remainder(adler_lane_a(a, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)) by {
   rewrite(adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)), adler_spec_a_u64(bytes, n, a_seed));
   known();
  }
  have to_integer(v1) == to_integer((bytes + n)[0 + 1] as int32) by normalize() using { to_integer(v1) == to_integer((bytes + n)[1] as int32); };
  have to_integer(v2) == to_integer((bytes + n)[0 + 2] as int32) by normalize() using { to_integer(v2) == to_integer((bytes + n)[2] as int32); };
  have to_integer(v3) == to_integer((bytes + n)[0 + 3] as int32) by normalize() using { to_integer(v3) == to_integer((bytes + n)[3] as int32); };
  apply(adler_native_four_lane_a_prefix_step(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), a, a0, a1, a2, a3, v0, v1, v2, v3)) using {
   0 <= 0; 0 <= 2147483643;
   0 <= adler_spec_a_u64(bytes, n, a_seed); adler_spec_a_u64(bytes, n, a_seed) <= 65520; 0 <= a;
   truncating_remainder(adler_lane_a(a, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed));
   to_integer(v0) == to_integer((bytes + n)[0] as int32); to_integer(a0) + to_integer(v0) <= 4294967295;
   to_integer(v1) == to_integer((bytes + n)[0 + 1] as int32); to_integer(a1) + to_integer(v1) <= 4294967295;
   to_integer(v2) == to_integer((bytes + n)[0 + 2] as int32); to_integer(a2) + to_integer(v2) <= 4294967295;
   to_integer(v3) == to_integer((bytes + n)[0 + 3] as int32); to_integer(a3) + to_integer(v3) <= 4294967295;
  };
  have to_integer(0 + 4) == to_integer(4u64) by normalize();
  apply(adler_spec_a_bridge(bytes + n, 0 + 4, 4u64, adler_spec_a_u64(bytes, n, a_seed))) using { to_integer(0 + 4) == to_integer(4u64); };
  have to_integer(n) + to_integer(4u64) <= 18446744073709551615 by solve() using { to_integer(n) + 4 <= 18446744073709551615; };
  apply(adler_spec_a_concat_u64(bytes, n, 4u64, a_seed)) using { to_integer(n) + to_integer(4u64) <= 18446744073709551615; 0 <= a_seed; };
  solve() using {
   truncating_remainder(adler_lane_a(a, to_integer((a0 + v0)), to_integer((a1 + v1)), to_integer((a2 + v2)), to_integer((a3 + v3))), 65521) == adler_spec_a(bytes + n, 0 + 4, adler_spec_a_u64(bytes, n, a_seed));
   adler_spec_a(bytes + n, 0 + 4, adler_spec_a_u64(bytes, n, a_seed)) == adler_spec_a_u64(bytes + n, 4u64, adler_spec_a_u64(bytes, n, a_seed));
   adler_spec_a_u64(bytes, n + 4u64, a_seed) == adler_spec_a_u64(bytes + n, 4u64, adler_spec_a_u64(bytes, n, a_seed));
  };
 }
}

theorem adler_native_deferred_b_prefix_step_u64(bytes: uint8[], n: uint64, pos: int32, a_seed: Integer, b_seed: Integer, a: uint32, b: uint32, a0: uint32, a1: uint32, a2: uint32, a3: uint32, b0: uint32, b1: uint32, b2: uint32, b3: uint32, v0: uint32, v1: uint32, v2: uint32, v3: uint32) {
 requires to_integer(n) + 4 <= 18446744073709551615;
 requires 0 <= pos;
 requires pos <= 22204;
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= b_seed;
 requires 0 <= adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3));
 requires truncating_remainder(adler_lane_a(to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a_u64(bytes, n, a_seed);
 requires truncating_remainder(adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)), 65521) == adler_spec_b_u64(bytes, n, a_seed, b_seed);
 requires to_integer(v0) == to_integer((bytes + n)[0] as int32);
 requires to_integer(a0) + to_integer(v0) <= 4294967295;
 requires to_integer(b0) + (to_integer(a0) + to_integer(v0)) <= 4294967295;
 requires to_integer(v1) == to_integer((bytes + n)[1] as int32);
 requires to_integer(a1) + to_integer(v1) <= 4294967295;
 requires to_integer(b1) + (to_integer(a1) + to_integer(v1)) <= 4294967295;
 requires to_integer(v2) == to_integer((bytes + n)[2] as int32);
 requires to_integer(a2) + to_integer(v2) <= 4294967295;
 requires to_integer(b2) + (to_integer(a2) + to_integer(v2)) <= 4294967295;
 requires to_integer(v3) == to_integer((bytes + n)[3] as int32);
 requires to_integer(a3) + to_integer(v3) <= 4294967295;
 requires to_integer(b3) + (to_integer(a3) + to_integer(v3)) <= 4294967295;
 ensures truncating_remainder(adler_lane_b(to_integer(b) + to_integer(pos + 4) * to_integer(a), to_integer(a1 + v1), to_integer(a2 + v2), to_integer(a3 + v3), to_integer(b0 + (a0 + v0)), to_integer(b1 + (a1 + v1)), to_integer(b2 + (a2 + v2)), to_integer(b3 + (a3 + v3))), 65521) == adler_spec_b_u64(bytes, n + 4u64, a_seed, b_seed) by {
  apply(adler_spec_a_canonical_u64(bytes, n, a_seed)) using { 0 <= a_seed; };
  apply(adler_spec_b_canonical_u64(bytes, n, a_seed, b_seed)) using { 0 <= a_seed; a_seed <= 65520; 0 <= b_seed; };
  apply(adler_spec_empty(bytes + n, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed))) using { 0 <= adler_spec_a_u64(bytes, n, a_seed); adler_spec_a_u64(bytes, n, a_seed) <= 65520; 0 <= adler_spec_b_u64(bytes, n, a_seed, b_seed); adler_spec_b_u64(bytes, n, a_seed, b_seed) <= 65520; };
  have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)) by {
   rewrite(adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)), adler_spec_a_u64(bytes, n, a_seed));
   known();
  }
  have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)), 65521) == adler_spec_b(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)) by {
   rewrite(adler_spec_b(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)), adler_spec_b_u64(bytes, n, a_seed, b_seed));
   known();
  }
  have to_integer(v1) == to_integer((bytes + n)[0 + 1] as int32) by normalize() using { to_integer(v1) == to_integer((bytes + n)[1] as int32); };
  have to_integer(v2) == to_integer((bytes + n)[0 + 2] as int32) by normalize() using { to_integer(v2) == to_integer((bytes + n)[2] as int32); };
  have to_integer(v3) == to_integer((bytes + n)[0 + 3] as int32) by normalize() using { to_integer(v3) == to_integer((bytes + n)[3] as int32); };
  apply(adler_native_deferred_b_prefix_step(bytes + n, 0, pos, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed), a, b, a0, a1, a2, a3, b0, b1, b2, b3, v0, v1, v2, v3)) using {
   0 <= 0; 0 <= 2147483643; 0 <= pos; pos <= 22204;
   0 <= adler_spec_a_u64(bytes, n, a_seed); adler_spec_a_u64(bytes, n, a_seed) <= 65520; 0 <= adler_spec_b_u64(bytes, n, a_seed, b_seed);
   0 <= adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3));
   truncating_remainder(adler_lane_a(to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed));
   truncating_remainder(adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)), 65521) == adler_spec_b(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed));
   to_integer(v0) == to_integer((bytes + n)[0] as int32); to_integer(a0) + to_integer(v0) <= 4294967295; to_integer(b0) + (to_integer(a0) + to_integer(v0)) <= 4294967295;
   to_integer(v1) == to_integer((bytes + n)[0 + 1] as int32); to_integer(a1) + to_integer(v1) <= 4294967295; to_integer(b1) + (to_integer(a1) + to_integer(v1)) <= 4294967295;
   to_integer(v2) == to_integer((bytes + n)[0 + 2] as int32); to_integer(a2) + to_integer(v2) <= 4294967295; to_integer(b2) + (to_integer(a2) + to_integer(v2)) <= 4294967295;
   to_integer(v3) == to_integer((bytes + n)[0 + 3] as int32); to_integer(a3) + to_integer(v3) <= 4294967295; to_integer(b3) + (to_integer(a3) + to_integer(v3)) <= 4294967295;
  };
  have to_integer(0 + 4) == to_integer(4u64) by normalize();
  apply(adler_spec_b_bridge(bytes + n, 0 + 4, 4u64, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed))) using { to_integer(0 + 4) == to_integer(4u64); };
  have to_integer(n) + to_integer(4u64) <= 18446744073709551615 by solve() using { to_integer(n) + 4 <= 18446744073709551615; };
  apply(adler_spec_b_concat_u64(bytes, n, 4u64, a_seed, b_seed)) using { to_integer(n) + to_integer(4u64) <= 18446744073709551615; 0 <= a_seed; a_seed <= 65520; 0 <= b_seed; };
  solve() using {
   truncating_remainder(adler_lane_b(to_integer(b) + to_integer(pos + 4) * to_integer(a), to_integer(a1 + v1), to_integer(a2 + v2), to_integer(a3 + v3), to_integer(b0 + (a0 + v0)), to_integer(b1 + (a1 + v1)), to_integer(b2 + (a2 + v2)), to_integer(b3 + (a3 + v3))), 65521) == adler_spec_b(bytes + n, 0 + 4, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed));
   adler_spec_b(bytes + n, 0 + 4, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)) == adler_spec_b_u64(bytes + n, 4u64, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed));
   adler_spec_b_u64(bytes, n + 4u64, a_seed, b_seed) == adler_spec_b_u64(bytes + n, 4u64, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed));
  };
 }
}

theorem adler_prefix_a_step_one_u64(bytes: uint8[], n: uint64, seed: Integer, representative: Integer) {
 requires to_integer(n) + 1 <= 18446744073709551615;
 requires 0 <= seed;
 requires 0 <= representative;
 requires truncating_remainder(representative, 65521) == adler_spec_a_u64(bytes, n, seed);
 ensures truncating_remainder(representative + to_integer((bytes + n)[0] as int32), 65521) == adler_spec_a_u64(bytes, n + 1u64, seed) by {
  apply(adler_spec_a_canonical_u64(bytes, n, seed)) using { 0 <= seed; };
  apply(adler_spec_empty(bytes + n, adler_spec_a_u64(bytes, n, seed), 0)) using { 0 <= adler_spec_a_u64(bytes, n, seed); adler_spec_a_u64(bytes, n, seed) <= 65520; 0 <= 0; 0 <= 65520; };
  have truncating_remainder(representative, 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, seed)) by {
   rewrite(adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, seed)), adler_spec_a_u64(bytes, n, seed));
   known();
  }
  apply(adler_prefix_a_step_one(bytes + n, 0, adler_spec_a_u64(bytes, n, seed), representative)) using { 0 <= 0; 0 <= 2147483646; 0 <= adler_spec_a_u64(bytes, n, seed); 0 <= representative; truncating_remainder(representative, 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, seed)); };
  have to_integer(0 + 1) == to_integer(1u64) by normalize();
  apply(adler_spec_a_bridge(bytes + n, 0 + 1, 1u64, adler_spec_a_u64(bytes, n, seed))) using { to_integer(0 + 1) == to_integer(1u64); };
  have to_integer(n) + to_integer(1u64) <= 18446744073709551615 by solve() using { to_integer(n) + 1 <= 18446744073709551615; };
  apply(adler_spec_a_concat_u64(bytes, n, 1u64, seed)) using { to_integer(n) + to_integer(1u64) <= 18446744073709551615; 0 <= seed; };
  solve() using {
   truncating_remainder(representative + to_integer((bytes + n)[0] as int32), 65521) == adler_spec_a(bytes + n, 0 + 1, adler_spec_a_u64(bytes, n, seed));
   adler_spec_a(bytes + n, 0 + 1, adler_spec_a_u64(bytes, n, seed)) == adler_spec_a_u64(bytes + n, 1u64, adler_spec_a_u64(bytes, n, seed));
   adler_spec_a_u64(bytes, n + 1u64, seed) == adler_spec_a_u64(bytes + n, 1u64, adler_spec_a_u64(bytes, n, seed));
  };
 }
}

theorem adler_prefix_b_step_one_u64(bytes: uint8[], n: uint64, a_seed: Integer, b_seed: Integer, a_rep: Integer, b_rep: Integer) {
 requires to_integer(n) + 1 <= 18446744073709551615;
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= b_seed;
 requires 0 <= a_rep;
 requires 0 <= b_rep;
 requires truncating_remainder(a_rep, 65521) == adler_spec_a_u64(bytes, n, a_seed);
 requires truncating_remainder(b_rep, 65521) == adler_spec_b_u64(bytes, n, a_seed, b_seed);
 ensures truncating_remainder((b_rep + a_rep + to_integer((bytes + n)[0] as int32)), 65521) == adler_spec_b_u64(bytes, n + 1u64, a_seed, b_seed) by {
  apply(adler_spec_a_canonical_u64(bytes, n, a_seed)) using { 0 <= a_seed; };
  apply(adler_spec_b_canonical_u64(bytes, n, a_seed, b_seed)) using { 0 <= a_seed; a_seed <= 65520; 0 <= b_seed; };
  apply(adler_spec_empty(bytes + n, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed))) using { 0 <= adler_spec_a_u64(bytes, n, a_seed); adler_spec_a_u64(bytes, n, a_seed) <= 65520; 0 <= adler_spec_b_u64(bytes, n, a_seed, b_seed); adler_spec_b_u64(bytes, n, a_seed, b_seed) <= 65520; };
  have truncating_remainder(a_rep, 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)) by {
   rewrite(adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)), adler_spec_a_u64(bytes, n, a_seed));
   known();
  }
  have truncating_remainder(b_rep, 65521) == adler_spec_b(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)) by {
   rewrite(adler_spec_b(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)), adler_spec_b_u64(bytes, n, a_seed, b_seed));
   known();
  }
  apply(adler_prefix_b_step_one(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed), a_rep, b_rep)) using { 0 <= 0; 0 <= 2147483646; 0 <= adler_spec_a_u64(bytes, n, a_seed); adler_spec_a_u64(bytes, n, a_seed) <= 65520; 0 <= adler_spec_b_u64(bytes, n, a_seed, b_seed); 0 <= a_rep; 0 <= b_rep; truncating_remainder(a_rep, 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)); truncating_remainder(b_rep, 65521) == adler_spec_b(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)); };
  have to_integer(0 + 1) == to_integer(1u64) by normalize();
  apply(adler_spec_b_bridge(bytes + n, 0 + 1, 1u64, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed))) using { to_integer(0 + 1) == to_integer(1u64); };
  have to_integer(n) + to_integer(1u64) <= 18446744073709551615 by solve() using { to_integer(n) + 1 <= 18446744073709551615; };
  apply(adler_spec_b_concat_u64(bytes, n, 1u64, a_seed, b_seed)) using { to_integer(n) + to_integer(1u64) <= 18446744073709551615; 0 <= a_seed; a_seed <= 65520; 0 <= b_seed; };
  solve() using {
   truncating_remainder((b_rep + a_rep + to_integer((bytes + n)[0] as int32)), 65521) == adler_spec_b(bytes + n, 0 + 1, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed));
   adler_spec_b(bytes + n, 0 + 1, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)) == adler_spec_b_u64(bytes + n, 1u64, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed));
   adler_spec_b_u64(bytes, n + 1u64, a_seed, b_seed) == adler_spec_b_u64(bytes + n, 1u64, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed));
  };
 }
}

// The byte count the chunks an iterator still holds stand for. The library model gives
// the iterator only as `len()` chunks; the proofs below keep counting remaining bytes.

function adler_chunk_bytes(count: uint64, size: uint64) -> uint64 { count * size }

theorem adler_chunk_bytes_none(size: uint64) {
 ensures adler_chunk_bytes(0u64, size) == 0u64 by { unfold(adler_chunk_bytes(0u64, size)); normalize(); }
}
theorem adler_chunk_bytes_exact_4(count: uint64, n: uint64) {
 requires count <= n / 4u64;
 ensures to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4 by {
  have n / 4u64 <= 4611686018427387903u64;
  have count <= 4611686018427387903u64;
  have to_integer(count * 4u64) == to_integer(count) * 4;
  unfold(adler_chunk_bytes(count, 4u64));
  known();
 }
}
theorem adler_chunk_bytes_exact_22208(count: uint64, n: uint64) {
 requires count <= n / 22208u64;
 ensures to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208 by {
  have n / 22208u64 <= 830635089774385u64;
  have count <= 830635089774385u64;
  have to_integer(count * 22208u64) == to_integer(count) * 22208;
  unfold(adler_chunk_bytes(count, 22208u64));
  known();
 }
}
theorem adler_quotient_4(n: uint64) {
 ensures to_integer(n / 4u64) * 4 == to_integer(n - n % 4u64) by {
  apply(integer::truncation_identity(to_integer(n), 4)) using { 4 != 0; };
  have to_integer(4u64) != 0 by { normalize(); }
  apply(integer::uint64_remainder_to_integer(n, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; };
  apply(integer::uint64_divide_to_integer(n, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; };
  have n % 4u64 <= n by normalize();
  have to_integer(n - (n % 4u64)) == to_integer(n) - to_integer((n % 4u64));
  rewrite(to_integer(n - n % 4u64), to_integer(n) - to_integer(n % 4u64));
  rewrite(to_integer(n % 4u64), truncating_remainder(to_integer(n), to_integer(4u64)));
  rewrite(to_integer(n / 4u64), truncating_quotient(to_integer(n), to_integer(4u64)));
  solve() using { to_integer(n) == truncating_quotient(to_integer(n), 4) * 4 + truncating_remainder(to_integer(n), 4); };
 }
}
theorem adler_quotient_22208(n: uint64) {
 ensures to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64) by {
  apply(integer::truncation_identity(to_integer(n), 22208)) using { 22208 != 0; };
  have to_integer(22208u64) != 0 by { normalize(); }
  apply(integer::uint64_remainder_to_integer(n, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; };
  apply(integer::uint64_divide_to_integer(n, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; };
  have n % 22208u64 <= n by normalize();
  have to_integer(n - (n % 22208u64)) == to_integer(n) - to_integer((n % 22208u64));
  rewrite(to_integer(n - n % 22208u64), to_integer(n) - to_integer(n % 22208u64));
  rewrite(to_integer(n % 22208u64), truncating_remainder(to_integer(n), to_integer(22208u64)));
  rewrite(to_integer(n / 22208u64), truncating_quotient(to_integer(n), to_integer(22208u64)));
  solve() using { to_integer(n) == truncating_quotient(to_integer(n), 22208) * 22208 + truncating_remainder(to_integer(n), 22208); };
 }
}
theorem adler_chunk_bytes_full_4(n: uint64) {
 ensures to_integer(adler_chunk_bytes(n / 4u64, 4u64)) == to_integer(n - n % 4u64) by {
  have n / 4u64 <= n / 4u64 by normalize();
  apply(adler_chunk_bytes_exact_4(n / 4u64, n));
  apply(adler_quotient_4(n));
  solve() using { to_integer(adler_chunk_bytes(n / 4u64, 4u64)) == to_integer(n / 4u64) * 4; to_integer(n / 4u64) * 4 == to_integer(n - n % 4u64); };
 }
}
theorem adler_chunk_bytes_whole_4(n: uint64) {
 requires n % 4u64 == 0u64;
 ensures adler_chunk_bytes(n / 4u64, 4u64) == n by {
  apply(adler_chunk_bytes_full_4(n));
  have to_integer(n - n % 4u64) == to_integer(n) by { rewrite(n % 4u64, 0u64); normalize(); }
  have to_integer(adler_chunk_bytes(n / 4u64, 4u64)) == to_integer(n) by solve() using { to_integer(adler_chunk_bytes(n / 4u64, 4u64)) == to_integer(n - n % 4u64); to_integer(n - n % 4u64) == to_integer(n); };
  known();
 }
}
theorem adler_chunk_bytes_next_4(count: uint64, n: uint64) {
 requires 0u64 < count;
 requires count <= n / 4u64;
 ensures 4u64 <= adler_chunk_bytes(count, 4u64) by {
  apply(adler_chunk_bytes_exact_4(count, n));
  solve() using { to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; 0u64 < count; };
 }
 ensures to_integer(adler_chunk_bytes(count - 1u64, 4u64)) == to_integer(adler_chunk_bytes(count, 4u64) - 4u64) by {
  apply(adler_chunk_bytes_exact_4(count, n));
  have to_integer(count - 1u64) == to_integer(count) - 1 by solve() using { 0u64 < count; };
  have to_integer(count - 1u64) <= to_integer(n / 4u64) by solve() using { to_integer(count - 1u64) == to_integer(count) - 1; count <= n / 4u64; };
  apply(adler_chunk_bytes_exact_4(count - 1u64, n));
  have 4u64 <= adler_chunk_bytes(count, 4u64) by solve() using { to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; 0u64 < count; };
  have to_integer(adler_chunk_bytes(count, 4u64) - 4u64) == to_integer(adler_chunk_bytes(count, 4u64)) - 4 by solve() using { 4u64 <= adler_chunk_bytes(count, 4u64); };
  solve() using { to_integer(adler_chunk_bytes(count - 1u64, 4u64)) == to_integer(count - 1u64) * 4; to_integer(count - 1u64) == to_integer(count) - 1; to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; to_integer(adler_chunk_bytes(count, 4u64) - 4u64) == to_integer(adler_chunk_bytes(count, 4u64)) - 4; };
 }
}
theorem adler_chunk_bytes_offset_4(count: uint64, n: uint64) {
 requires count <= n / 4u64;
 ensures to_integer(adler_chunk_bytes(count, 4u64)) <= to_integer(n - n % 4u64) by {
  apply(adler_chunk_bytes_exact_4(count, n));
  apply(adler_quotient_4(n));
  solve() using { to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; to_integer(n / 4u64) * 4 == to_integer(n - n % 4u64); count <= n / 4u64; };
 }
 ensures to_integer((n / 4u64 - count) * 4u64) == to_integer((n - n % 4u64) - adler_chunk_bytes(count, 4u64)) by {
  apply(adler_chunk_bytes_exact_4(count, n));
  apply(adler_quotient_4(n));
  have to_integer(n / 4u64 - count) == to_integer(n / 4u64) - to_integer(count) by solve() using { count <= n / 4u64; };
  have n / 4u64 <= 4611686018427387903u64;
  have n / 4u64 - count <= 4611686018427387903u64 by solve() using { n / 4u64 <= 4611686018427387903u64; count <= n / 4u64; to_integer(n / 4u64 - count) == to_integer(n / 4u64) - to_integer(count); };
  have to_integer((n / 4u64 - count) * 4u64) == to_integer(n / 4u64 - count) * 4;
  have to_integer(adler_chunk_bytes(count, 4u64)) <= to_integer(n - n % 4u64) by solve() using { to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; to_integer(n / 4u64) * 4 == to_integer(n - n % 4u64); count <= n / 4u64; };
  apply(integer::uint64_subtract_to_integer(n - n % 4u64, adler_chunk_bytes(count, 4u64)));
  solve() using { to_integer((n / 4u64 - count) * 4u64) == to_integer(n / 4u64 - count) * 4; to_integer(n / 4u64 - count) == to_integer(n / 4u64) - to_integer(count); to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; to_integer(n / 4u64) * 4 == to_integer(n - n % 4u64); to_integer((n - n % 4u64) - adler_chunk_bytes(count, 4u64)) == to_integer(n - n % 4u64) - to_integer(adler_chunk_bytes(count, 4u64)); };
 }
}
theorem adler_chunk_bytes_offset_whole_4(count: uint64, n: uint64) {
 requires count <= n / 4u64;
 requires n % 4u64 == 0u64;
 ensures adler_chunk_bytes(count, 4u64) <= n by {
  apply(adler_chunk_bytes_offset_4(count, n));
  have to_integer(n - n % 4u64) == to_integer(n) by { rewrite(n % 4u64, 0u64); normalize(); }
  solve() using { to_integer(adler_chunk_bytes(count, 4u64)) <= to_integer(n - n % 4u64); to_integer(n - n % 4u64) == to_integer(n); };
 }
 ensures to_integer((n / 4u64 - count) * 4u64) == to_integer(n - adler_chunk_bytes(count, 4u64)) by {
  apply(adler_chunk_bytes_offset_4(count, n));
  rewrite(to_integer((n / 4u64 - count) * 4u64), to_integer((n - n % 4u64) - adler_chunk_bytes(count, 4u64)));
  rewrite(n % 4u64, 0u64);
  normalize();
 }
}
theorem adler_chunk_bytes_full_22208(n: uint64) {
 ensures to_integer(adler_chunk_bytes(n / 22208u64, 22208u64)) == to_integer(n - n % 22208u64) by {
  have n / 22208u64 <= n / 22208u64 by normalize();
  apply(adler_chunk_bytes_exact_22208(n / 22208u64, n));
  apply(adler_quotient_22208(n));
  solve() using { to_integer(adler_chunk_bytes(n / 22208u64, 22208u64)) == to_integer(n / 22208u64) * 22208; to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64); };
 }
}
theorem adler_chunk_bytes_whole_22208(n: uint64) {
 requires n % 22208u64 == 0u64;
 ensures adler_chunk_bytes(n / 22208u64, 22208u64) == n by {
  apply(adler_chunk_bytes_full_22208(n));
  have to_integer(n - n % 22208u64) == to_integer(n) by { rewrite(n % 22208u64, 0u64); normalize(); }
  have to_integer(adler_chunk_bytes(n / 22208u64, 22208u64)) == to_integer(n) by solve() using { to_integer(adler_chunk_bytes(n / 22208u64, 22208u64)) == to_integer(n - n % 22208u64); to_integer(n - n % 22208u64) == to_integer(n); };
  known();
 }
}
theorem adler_chunk_bytes_next_22208(count: uint64, n: uint64) {
 requires 0u64 < count;
 requires count <= n / 22208u64;
 ensures 22208u64 <= adler_chunk_bytes(count, 22208u64) by {
  apply(adler_chunk_bytes_exact_22208(count, n));
  solve() using { to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; 0u64 < count; };
 }
 ensures to_integer(adler_chunk_bytes(count - 1u64, 22208u64)) == to_integer(adler_chunk_bytes(count, 22208u64) - 22208u64) by {
  apply(adler_chunk_bytes_exact_22208(count, n));
  have to_integer(count - 1u64) == to_integer(count) - 1 by solve() using { 0u64 < count; };
  have to_integer(count - 1u64) <= to_integer(n / 22208u64) by solve() using { to_integer(count - 1u64) == to_integer(count) - 1; count <= n / 22208u64; };
  apply(adler_chunk_bytes_exact_22208(count - 1u64, n));
  have 22208u64 <= adler_chunk_bytes(count, 22208u64) by solve() using { to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; 0u64 < count; };
  have to_integer(adler_chunk_bytes(count, 22208u64) - 22208u64) == to_integer(adler_chunk_bytes(count, 22208u64)) - 22208 by solve() using { 22208u64 <= adler_chunk_bytes(count, 22208u64); };
  solve() using { to_integer(adler_chunk_bytes(count - 1u64, 22208u64)) == to_integer(count - 1u64) * 22208; to_integer(count - 1u64) == to_integer(count) - 1; to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; to_integer(adler_chunk_bytes(count, 22208u64) - 22208u64) == to_integer(adler_chunk_bytes(count, 22208u64)) - 22208; };
 }
}
theorem adler_chunk_bytes_offset_22208(count: uint64, n: uint64) {
 requires count <= n / 22208u64;
 ensures to_integer(adler_chunk_bytes(count, 22208u64)) <= to_integer(n - n % 22208u64) by {
  apply(adler_chunk_bytes_exact_22208(count, n));
  apply(adler_quotient_22208(n));
  solve() using { to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64); count <= n / 22208u64; };
 }
 ensures to_integer((n / 22208u64 - count) * 22208u64) == to_integer((n - n % 22208u64) - adler_chunk_bytes(count, 22208u64)) by {
  apply(adler_chunk_bytes_exact_22208(count, n));
  apply(adler_quotient_22208(n));
  have to_integer(n / 22208u64 - count) == to_integer(n / 22208u64) - to_integer(count) by solve() using { count <= n / 22208u64; };
  have n / 22208u64 <= 830635089774385u64;
  have n / 22208u64 - count <= 830635089774385u64 by solve() using { n / 22208u64 <= 830635089774385u64; count <= n / 22208u64; to_integer(n / 22208u64 - count) == to_integer(n / 22208u64) - to_integer(count); };
  have to_integer((n / 22208u64 - count) * 22208u64) == to_integer(n / 22208u64 - count) * 22208;
  have to_integer(adler_chunk_bytes(count, 22208u64)) <= to_integer(n - n % 22208u64) by solve() using { to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64); count <= n / 22208u64; };
  apply(integer::uint64_subtract_to_integer(n - n % 22208u64, adler_chunk_bytes(count, 22208u64)));
  solve() using { to_integer((n / 22208u64 - count) * 22208u64) == to_integer(n / 22208u64 - count) * 22208; to_integer(n / 22208u64 - count) == to_integer(n / 22208u64) - to_integer(count); to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64); to_integer((n - n % 22208u64) - adler_chunk_bytes(count, 22208u64)) == to_integer(n - n % 22208u64) - to_integer(adler_chunk_bytes(count, 22208u64)); };
 }
}
theorem adler_chunk_bytes_offset_whole_22208(count: uint64, n: uint64) {
 requires count <= n / 22208u64;
 requires n % 22208u64 == 0u64;
 ensures adler_chunk_bytes(count, 22208u64) <= n by {
  apply(adler_chunk_bytes_offset_22208(count, n));
  have to_integer(n - n % 22208u64) == to_integer(n) by { rewrite(n % 22208u64, 0u64); normalize(); }
  solve() using { to_integer(adler_chunk_bytes(count, 22208u64)) <= to_integer(n - n % 22208u64); to_integer(n - n % 22208u64) == to_integer(n); };
 }
 ensures to_integer((n / 22208u64 - count) * 22208u64) == to_integer(n - adler_chunk_bytes(count, 22208u64)) by {
  apply(adler_chunk_bytes_offset_22208(count, n));
  rewrite(to_integer((n / 22208u64 - count) * 22208u64), to_integer((n - n % 22208u64) - adler_chunk_bytes(count, 22208u64)));
  rewrite(n % 22208u64, 0u64);
  normalize();
 }
}

theorem adler_uint64_pointer_association(base: const uint8*, p: uint64, q: uint64) {
 requires to_integer(p) + to_integer(q) <= 18446744073709551615;
 ensures (base + p) + q == base + (p + q) by {
  apply(integer::uint64_add_to_integer(p, q));
  solve() using { to_integer(p + q) == to_integer(p) + to_integer(q); };
 }
}
theorem adler_tail_pointer_position(base: const uint8*, p: uint64, n: uint64, r: uint64) {
 requires to_integer(p) <= to_integer(n);
 requires to_integer(r) <= to_integer(n - p);
 ensures (base + p) + ((n - p) - r) == base + (n - r) by {
  have to_integer(n - p) == to_integer(n) - to_integer(p);
  have to_integer((n - p) - r) == to_integer(n - p) - to_integer(r);
  have to_integer(r) <= to_integer(n);
  have to_integer(n - r) == to_integer(n) - to_integer(r);
  have to_integer(p + ((n - p) - r)) == to_integer(p) + to_integer((n - p) - r);
  have to_integer(p + ((n - p) - r)) == to_integer(n - r);
  have to_integer(p) + to_integer((n - p) - r) <= 18446744073709551615;
  apply(adler_uint64_pointer_association(base, p, (n - p) - r));
  rewrite((base + p) + ((n - p) - r), base + (p + ((n - p) - r)));
  solve() using { to_integer(p + ((n - p) - r)) == to_integer(n - r); };
 }
}
theorem adler_tail_read_offset(p: uint64, n: uint64, length: uint64, r: uint64) {
 requires to_integer(p) <= to_integer(n);
 requires to_integer(length) == to_integer(n - p);
 requires 1u64 <= r;
 requires r <= length;
 ensures to_integer(p + (length - r)) < to_integer(n) by {
  have to_integer(n - p) == to_integer(n) - to_integer(p);
  have to_integer(length - r) == to_integer(length) - to_integer(r);
  have to_integer(p) + to_integer(length - r) <= 18446744073709551615;
  apply(integer::uint64_add_to_integer(p, length - r));
  solve();
 }
}

impl adler2::Adler32 {
    fn compute(&mut self, bytes: &[u8]) {
     requires (self.a as u32) <= 65520u32;
     requires (self.b as u32) <= 65520u32;
     owns self.a; owns self.b; views *bytes;
     ensures self.a < 65521;
     ensures self.b < 65521;
     ensures to_integer(self.a) <= 65520;
     ensures to_integer(self.b) <= 65520;
     ensures to_integer(self.a) == old(adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32)))));
     ensures to_integer(self.b) == old(adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
    } by {
     apply(adler_general_prefix_divisible_u64(bytes.len()));
     apply(adler_outer_bulk_divisible_u64((bytes.len() - bytes.len() % 4u64)));
     have bytes.len() % 4u64 <= bytes.len() by normalize();
     step_until(assignment(b, 0)); step();
     have a <= 65520u32;
     have b <= 65520u32;
     step_until(loop(0));
     // The outer iterator, its length and its saved remainder, from the library contract.
     have loop(0).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64);
     have loop(0).iter.len() == (bytes.len() - bytes.len() % 4u64) / 22208u64 by {
      apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64));
      solve();
     }
     apply(adler_chunk_bytes_full_22208((bytes.len() - bytes.len() % 4u64)));
     have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) by { rewrite(loop(0).iter.len(), (bytes.len() - bytes.len() % 4u64) / 22208u64); known(); }
     have 22208u64 == 22208u64;
     have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64 by { rewrite(to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64))); known(); }
     have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64 by {
      apply(chunks_exact::remainder_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64));
      solve();
     }
     have remainder_len == bytes.len() % 4u64;
     have bytes == old(bytes) by known();
     have bytes.len() == old(bytes.len()) by known();
     have to_integer(a_vec.0[0]) <= 65520;
     have to_integer(a_vec.0[1]) <= 65520;
     have to_integer(a_vec.0[2]) <= 65520;
     have to_integer(a_vec.0[3]) <= 65520;
     have to_integer(b_vec.0[0]) <= 65520;
     have to_integer(b_vec.0[1]) <= 65520;
     have to_integer(b_vec.0[2]) <= 65520;
     have to_integer(b_vec.0[3]) <= 65520;
     have to_integer(__rust_checked_93) == to_integer(bytes.len() - bytes.len() % 4u64);
     have __rust_checked_94 == 22208u64;
     have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) by {
      apply(chunks_exact::remainder_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64));
      solve();
     }
     have to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64)) by normalize();
     have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)) by normalize() using { to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64)); };
     have to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len()) by solve() using { bytes.len() % 4u64 <= bytes.len(); };
     have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len()) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64));  to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)); to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len()); };
     have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) by { rewrite(to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64))); normalize(); }
     apply(adler_uint64_self_subtract(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)));
     have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(0u64) by { rewrite(to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64))); known(); }
     // Establish the empty original-input prefix before the full-batch loop.
     apply(adler_spec_empty_u64(bytes, to_integer(a), 0)) using { 0 <= to_integer(a); to_integer(a) <= 65520; 0 <= 0; 0 <= 65520; };
     have to_integer(a_vec.0[0]) == 0;
     have to_integer(a_vec.0[1]) == 0;
     have to_integer(a_vec.0[2]) == 0;
     have to_integer(a_vec.0[3]) == 0;
     have adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) == to_integer(a) by { unfold(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); solve() using { to_integer(a_vec.0[0]) == 0; to_integer(a_vec.0[1]) == 0; to_integer(a_vec.0[2]) == 0; to_integer(a_vec.0[3]) == 0; }; }
     have to_integer(a) == 0 * 65521 + to_integer(a) by solve() using {};
     apply(adler_residue_unique(to_integer(a), 0, to_integer(a))) using { 0 <= to_integer(a); to_integer(a) == 0 * 65521 + to_integer(a); to_integer(a) <= 65520; };
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a)) by { rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(0u64)); rewrite(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), to_integer(a)); solve() using { truncating_remainder(to_integer(a), 65521) == to_integer(a); adler_spec_a_u64(bytes, 0u64, to_integer(a)) == to_integer(a); }; }
     // Keep the entry B seed fixed while the working scalar B is reduced.
     have to_integer(b) == old(to_integer((self.b as u32))) by solve();
     have 0 <= old(to_integer((self.b as u32))) by solve() using { 0 <= to_integer(b); to_integer(b) == old(to_integer((self.b as u32))); };
     have old(to_integer((self.b as u32))) <= 65520 by solve() using { to_integer(b) <= 65520; to_integer(b) == old(to_integer((self.b as u32))); };
     apply(adler_spec_empty_u64(bytes, to_integer(a), old(to_integer((self.b as u32))))) using { 0 <= to_integer(a); to_integer(a) <= 65520; 0 <= old(to_integer((self.b as u32))); old(to_integer((self.b as u32))) <= 65520; };
     have to_integer(b_vec.0[0]) == 0;
     have to_integer(b_vec.0[1]) == 0;
     have to_integer(b_vec.0[2]) == 0;
     have to_integer(b_vec.0[3]) == 0;
     apply(adler_zero_lane_b_residue(to_integer(b))) using { 0 <= to_integer(b); to_integer(b) <= 65520; };
     have adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) == adler_lane_b(to_integer(b), 0, 0, 0, 0, 0, 0, 0) by {
      rewrite(to_integer(a_vec.0[1]), 0);
      rewrite(to_integer(a_vec.0[2]), 0);
      rewrite(to_integer(a_vec.0[3]), 0);
      rewrite(to_integer(b_vec.0[0]), 0);
      rewrite(to_integer(b_vec.0[1]), 0);
      rewrite(to_integer(b_vec.0[2]), 0);
      rewrite(to_integer(b_vec.0[3]), 0);
      normalize();
     }
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(0u64)); rewrite(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), adler_lane_b(to_integer(b), 0, 0, 0, 0, 0, 0, 0)); solve() using { truncating_remainder(adler_lane_b(to_integer(b), 0, 0, 0, 0, 0, 0, 0), 65521) == to_integer(b); adler_spec_b_u64(bytes, 0u64, to_integer(a), old(to_integer((self.b as u32)))) == old(to_integer((self.b as u32))); to_integer(b) == old(to_integer((self.b as u32))); }; }
     have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) } by solve();
     have loop(0).iter.len() <= (bytes.len() - bytes.len() % 4u64) / 22208u64;
     loop {
     decreases loop(0).iter.len();
     invariant to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len());
     invariant to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
     owns a_vec.0[0..4]; owns b_vec.0[0..4];
     views *bytes;
     invariant bytes == old(bytes);
     invariant forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
     invariant bytes.len() == old(bytes.len());
     invariant a <= 65520u32;
     invariant b <= 65520u32;
     invariant adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
     invariant remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
     invariant to_integer(__rust_checked_93) == to_integer(bytes.len() - bytes.len() % 4u64);
     invariant __rust_checked_94 == 22208u64;
     invariant remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
     invariant remainder_len == bytes.len() % 4u64;
     invariant to_integer(a_vec.0[0]) <= 65520;
     invariant to_integer(a_vec.0[1]) <= 65520;
     invariant to_integer(a_vec.0[2]) <= 65520;
     invariant to_integer(a_vec.0[3]) <= 65520;
     invariant to_integer(b_vec.0[0]) <= 65520;
     invariant to_integer(b_vec.0[1]) <= 65520;
     invariant to_integer(b_vec.0[2]) <= 65520;
     invariant to_integer(b_vec.0[3]) <= 65520;
     invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a));
     invariant 0 <= old(to_integer((self.b as u32)));
     invariant truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32))));
     invariant loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), iterations);
     invariant to_integer(loop(0).iter.len()) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64);

     initialize by {
      have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len());
      have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
      have bytes == old(bytes);
      have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
      have bytes.len() == old(bytes.len());
      have a <= 65520u32;
      have b <= 65520u32;
      have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
      have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
      have to_integer(__rust_checked_93) == to_integer(bytes.len() - bytes.len() % 4u64);
      have __rust_checked_94 == 22208u64;
      have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
      have remainder_len == bytes.len() % 4u64;
      have to_integer(a_vec.0[0]) <= 65520;
      have to_integer(a_vec.0[1]) <= 65520;
      have to_integer(a_vec.0[2]) <= 65520;
      have to_integer(a_vec.0[3]) <= 65520;
      have to_integer(b_vec.0[0]) <= 65520;
      have to_integer(b_vec.0[1]) <= 65520;
      have to_integer(b_vec.0[2]) <= 65520;
      have to_integer(b_vec.0[3]) <= 65520;
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a));
      have 0 <= old(to_integer((self.b as u32)));
      have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32))));
      have loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), iterations) by {
       apply(chunks_exact::after_zero(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64)));
       have loop(0).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64);
       solve();
      }
      have to_integer(loop(0).iter.len()) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64);
     }
     preserve by {
      mark outer_pass;
      // The header reads `iter.len()` and leaves by `break` when it is zero.
      step(); step(); step(); step();
      if 0u64 < loop(0).iter.len() {
      have chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64).len() == (bytes.len() - bytes.len() % 4u64) / 22208u64 by {
       apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64));
      }
      have loop(0).iter.len() <= (bytes.len() - bytes.len() % 4u64) / 22208u64 by solve() using { to_integer(loop(0).iter.len()) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64); 0 <= iterations; };
      apply(integer::uint64_subtract_to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64, loop(0).iter.len()));
      have to_integer(((bytes.len() - bytes.len() % 4u64) / 22208u64 - loop(0).iter.len())) == iterations by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) / 22208u64 - loop(0).iter.len())) == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len()); to_integer(loop(0).iter.len()) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64); };
      have ((bytes.len() - bytes.len() % 4u64) / 22208u64 - loop(0).iter.len()) < chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64).len() by solve() using { chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64).len() == (bytes.len() - bytes.len() % 4u64) / 22208u64; 0u64 < loop(0).iter.len(); loop(0).iter.len() <= (bytes.len() - bytes.len() % 4u64) / 22208u64; };
      have loop(0).iter.nth(0u64) == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64).nth(((bytes.len() - bytes.len() % 4u64) / 22208u64 - loop(0).iter.len())) by {
       apply(chunks_exact::nth_after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), iterations, 0u64, ((bytes.len() - bytes.len() % 4u64) / 22208u64 - loop(0).iter.len())));
       solve();
      }
      have loop(0).iter.nth(0u64).len() == 22208u64 by {
       apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64, ((bytes.len() - bytes.len() % 4u64) / 22208u64 - loop(0).iter.len())));
       solve();
      }
      have loop(0).iter.after_next() == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), iterations + 1) by {
       apply(chunks_exact::after_next_after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), iterations));
       solve();
      }
      have loop(0).iter.after_next().len() == loop(0).iter.len() - 1u64 by {
       apply(chunks_exact::len_after_next(loop(0).iter));
      }
      apply(adler_chunk_bytes_next_22208(loop(0).iter.len(), (bytes.len() - bytes.len() % 4u64)));
      apply(adler_chunk_bytes_offset_22208(loop(0).iter.len(), (bytes.len() - bytes.len() % 4u64)));
      have 22208u64 <= adler_chunk_bytes(loop(0).iter.len(), 22208u64);
      have 0u64 < adler_chunk_bytes(loop(0).iter.len(), 22208u64) by solve() using { 22208u64 <= adler_chunk_bytes(loop(0).iter.len(), 22208u64); };
      // The first fact about the batch pointer is its offset from `bytes`; the inner loop takes its
      // view of the batch out of the input's view at that offset.
      have loop(0).iter.nth(0u64).as_ptr() == (bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) by {
       have loop(0).iter.nth(0u64).as_ptr() == bytes + ((bytes.len() - bytes.len() % 4u64) / 22208u64 - loop(0).iter.len()) * 22208u64 by {
        apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64, ((bytes.len() - bytes.len() % 4u64) / 22208u64 - loop(0).iter.len())));
        solve();
       }
       rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(((bytes.len() - bytes.len() % 4u64) / 22208u64 - loop(0).iter.len()) * 22208u64));
       known();
      }
      apply(integer::uint64_subtract_to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64), adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
      have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22208 <= to_integer(bytes.len()) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) - to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)); 22208u64 <= adler_chunk_bytes(loop(0).iter.len(), 22208u64); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len()); };
      have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) < to_integer(bytes.len()) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22208 <= to_integer(bytes.len()); };
      have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + to_integer(22207u64) <= 18446744073709551615 by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22208 <= to_integer(bytes.len()); };
      apply(integer::uint64_add_to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), 22207u64));
      have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22207u64) < to_integer(bytes.len()) by solve() using { to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22207u64) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + to_integer(22207u64); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22208 <= to_integer(bytes.len()); };
      mark outer_head;
      have at(outer_head, loop(0).iter.nth(0u64).as_ptr()) == at(outer_head, (bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))));
      have at(outer_head, loop(0).iter.nth(0u64).len()) == 22208u64;
      have 0u64 < at(outer_head, loop(0).iter.len());
      have to_integer(adler_chunk_bytes(at(outer_head, loop(0).iter.len()) - 1u64, 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64);
      have at(outer_head, loop(0).iter.after_next()) == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), iterations + 1);
      have to_integer(at(outer_head, loop(0).iter.len())) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64);
      have to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
      have at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) % 22208u64 == 0u64;
      have 22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      have at(outer_head, (bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
      step_until(loop(1));
      have chunk_len == 22208u64;

      have chunk == at(outer_head, (bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))));
      have loop(0).iter == at(outer_head, loop(0).iter.after_next());
      have loop(0).iter.len() == at(outer_head, loop(0).iter.len()) - 1u64;
      have loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), iterations + 1);
      have to_integer(loop(0).iter.len()) + (iterations + 1) == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) by solve() using { loop(0).iter.len() == at(outer_head, loop(0).iter.len()) - 1u64; 0u64 < at(outer_head, loop(0).iter.len()); to_integer(at(outer_head, loop(0).iter.len())) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64); };
      have loop(0).iter.len() <= (bytes.len() - bytes.len() % 4u64) / 22208u64;
      // Inside the inner loop `iterations` counts its passes, so the outer iterator's
      // position is carried there by its length.
      have (to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len())) == iterations + 1 by solve() using { to_integer(loop(0).iter.len()) + (iterations + 1) == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64); };
      have loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), (to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len()))) by { rewrite((to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len())), iterations + 1); known(); }
      // The inner iterator covers this 22208-byte chunk in 5552 four-byte chunks.
      have loop(1).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64);
      have loop(1).iter.len() == chunk_len / 4u64 by {
       apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64));
       solve();
      }
      have chunk_len % 4u64 == 0u64 by { rewrite(chunk_len, 22208u64); normalize(); }
      apply(adler_chunk_bytes_whole_4(chunk_len));
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) == chunk_len by { rewrite(loop(1).iter.len(), chunk_len / 4u64); known(); }
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) == 22208u64 by solve() using { adler_chunk_bytes(loop(1).iter.len(), 4u64) == chunk_len; chunk_len == 22208u64; };
      have loop(1).iter.len() <= chunk_len / 4u64;
     have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) == 22208 by { rewrite(adler_chunk_bytes(loop(1).iter.len(), 4u64), 22208u64); normalize(); }
      have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == chunk by { rewrite(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32), 22208); solve(); }
     have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64) by { rewrite(loop(0).iter.len(), at(outer_head, loop(0).iter.len()) - 1u64); known(); }
     apply(adler_outer_remaining_step_divisible_u64(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) using { 22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)); at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) % 22208u64 == 0u64; };
     have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64 by { rewrite(to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64)); known(); }

      have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64));
       to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64);
       22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
      };
      have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(bytes.len()) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64));  to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len()); };
      have to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64));
       22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len());
      };
      have chunk == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) by { rewrite(chunk, at(outer_head, (bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); known(); }
      have to_integer(22208u64) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64));
       to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64);
       to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
       22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
      };
      have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) == to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64));
       to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64);
       to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
       22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
       to_integer(22208u64) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      };
      have chunk == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) by { rewrite(to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)), to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); known(); }
      have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) <= to_integer(bytes.len()) by { rewrite(to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)), to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); known(); }
      have to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) by { rewrite(to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)), to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); known(); }
      mark outer_chunk;
      // The batch continues the uint64 running prefix at the batch cursor.
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(a)) by solve();
      have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(a), old(to_integer((self.b as u32)))) by solve();
      have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) by { rewrite(adler_chunk_bytes(loop(1).iter.len(), 4u64), 22208u64); known(); }
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a)) by { rewrite(to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)), to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); known(); }
      have 4u64 == 4u64;
      have chunk == at(outer_chunk, chunk);
      have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(outer_chunk, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      have (bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) == at(outer_chunk, (bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))));
     apply(adler_lane_initial_ceiling());
     apply(adler_lane_iterator_initial(22208));
     have adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == 0 by { rewrite(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32), 22208); known(); }
     have to_integer(a_vec.0[0]) <= 65520;
     have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); solve() using { to_integer(a_vec.0[0]) <= 65520; }; }
     have to_integer(b_vec.0[0]) <= 65520;
     have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); solve() using { to_integer(b_vec.0[0]) <= 65520; }; }
     have to_integer(a_vec.0[1]) <= 65520;
     have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); solve() using { to_integer(a_vec.0[1]) <= 65520; }; }
     have to_integer(b_vec.0[1]) <= 65520;
     have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); solve() using { to_integer(b_vec.0[1]) <= 65520; }; }
     have to_integer(a_vec.0[2]) <= 65520;
     have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); solve() using { to_integer(a_vec.0[2]) <= 65520; }; }
     have to_integer(b_vec.0[2]) <= 65520;
     have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); solve() using { to_integer(b_vec.0[2]) <= 65520; }; }
     have to_integer(a_vec.0[3]) <= 65520;
     have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); solve() using { to_integer(a_vec.0[3]) <= 65520; }; }
     have to_integer(b_vec.0[3]) <= 65520;
     have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); solve() using { to_integer(b_vec.0[3]) <= 65520; }; }
     have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) by { rewrite(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32), 22208); normalize() using {}; }
     have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208 by { rewrite(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32), 22208); normalize() using {}; }
     have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208 by known();
     have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by { rewrite(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32), 22208); normalize() using {}; }
     have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == at(outer_chunk, chunk) + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32));
     have chunk_len < 22209u64;
     have chunk_len == 22208u64 by known();
     have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64;
     have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by {
      rewrite((chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))), chunk);
      rewrite(adler_chunk_bytes(loop(1).iter.len(), 4u64), 22208u64);
      rewrite(chunk, bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)); normalize();
     }
     have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); };
     have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) <= to_integer(bytes.len()) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len()); };
     have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) <= to_integer(18446744073709529407u64) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64)); 22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)); to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); };
     have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) == to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) + 22208u64) by solve() using { to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64); 22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)); bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); };
     // B keeps the batch-local scalar contribution deferred until Rust adds it.
     have 0 <= to_integer(b);
     have to_integer(b) <= 4294967295;
     have 0 <= to_integer((b_vec.0[0]));
     have to_integer((b_vec.0[0])) <= 4294967295;
     have 0 <= to_integer((b_vec.0[1]));
     have to_integer((b_vec.0[1])) <= 4294967295;
     have 0 <= to_integer((b_vec.0[2]));
     have to_integer((b_vec.0[2])) <= 4294967295;
     have 0 <= to_integer((b_vec.0[3]));
     have to_integer((b_vec.0[3])) <= 4294967295;
     apply(adler_canonical_lane_b_floor(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]))) using { 0 <= to_integer(b); to_integer(a_vec.0[1]) <= 65520; to_integer(a_vec.0[2]) <= 65520; to_integer(a_vec.0[3]) <= 65520; 0 <= to_integer(b_vec.0[0]); 0 <= to_integer(b_vec.0[1]); 0 <= to_integer(b_vec.0[2]); 0 <= to_integer(b_vec.0[3]); };
     have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { apply(adler_empty_full_batch_position(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) using { ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) == 22208; }; rewrite(to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); have to_integer(b) + 0 * to_integer(a) == to_integer(b) by solve() using {}; rewrite(to_integer(b) + 0 * to_integer(a), to_integer(b)); known(); }
     apply(adler_empty_full_batch_position(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) using { ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) == 22208; };
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)), to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))), 0); have to_integer(b) + 0 * to_integer(a) == to_integer(b) by solve() using {}; rewrite(to_integer(b) + 0 * to_integer(a), to_integer(b)); solve(); }
     have defined(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32));
     loop {
      decreases loop(1).iter.len();
     invariant adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64;
     invariant to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
     invariant to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len());
      owns a_vec.0[0..4];
      owns b_vec.0[0..4];
      views bytes[0..(bytes.len() - bytes.len() % 4u64)];
      invariant (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64));
      invariant to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
      invariant chunk == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64);
      invariant to_integer(22208u64) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      invariant to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) <= to_integer(bytes.len());
      invariant to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64));
      invariant chunk_len == 22208u64;
      invariant chunk == at(loop(1).entry, chunk);
      invariant bytes == old(bytes);
     invariant forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
      invariant bytes.len() == old(bytes.len());
      invariant adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(loop(1).entry, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      invariant adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
      invariant remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
     invariant to_integer(__rust_checked_93) == to_integer(bytes.len() - bytes.len() % 4u64);
     invariant __rust_checked_94 == 22208u64;
      invariant remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
      invariant remainder_len == bytes.len() % 4u64;
      invariant a <= 65520u32;
      invariant b <= 65520u32;
      invariant 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208;
      invariant ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
      invariant to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
      invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a));
      invariant 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
      invariant loop(0).iter.len() == at(loop(1).entry, loop(0).iter.len());
      invariant loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), (to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len())));
      invariant loop(1).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64), iterations);
      invariant to_integer(loop(1).iter.len()) + iterations == to_integer(chunk_len / 4u64);

      initialize by {
       have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64;
       have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
       have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len());
       have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by { known(); known(); }
       have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
       have chunk == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64);
       have to_integer(22208u64) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) <= to_integer(bytes.len());
       have to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64));
       have chunk_len == 22208u64;
       have chunk == at(loop(1).entry, chunk);
       have bytes == old(bytes);
       have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
       have bytes.len() == old(bytes.len());
       have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(loop(1).entry, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
       have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
       have to_integer(__rust_checked_93) == to_integer(bytes.len() - bytes.len() % 4u64);
       have __rust_checked_94 == 22208u64;
       have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
       have remainder_len == bytes.len() % 4u64;
       have a <= 65520u32;
       have b <= 65520u32;
       have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208;
       have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a));
       have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
       have 0 <= old(to_integer((self.b as u32)));
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
       have loop(0).iter.len() == at(loop(1).entry, loop(0).iter.len());
       have loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), (to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len())));
       have loop(1).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64), iterations) by {
        apply(chunks_exact::after_zero(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64)));
        have loop(1).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64);
        solve();
       }
       have to_integer(loop(1).iter.len()) + iterations == to_integer(chunk_len / 4u64);
      }
     preserve by {
       mark inner_pass;
       // The header reads `iter.len()` and leaves by `break` when it is zero.
       step(); step(); step(); step();
       if 0u64 < loop(1).iter.len() {
        have chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64).len() == chunk_len / 4u64 by {
         apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64));
        }
        have loop(1).iter.len() <= chunk_len / 4u64 by solve() using { to_integer(loop(1).iter.len()) + iterations == to_integer(chunk_len / 4u64); 0 <= iterations; };
        apply(integer::uint64_subtract_to_integer(chunk_len / 4u64, loop(1).iter.len()));
        have to_integer((chunk_len / 4u64 - loop(1).iter.len())) == iterations by solve() using { to_integer((chunk_len / 4u64 - loop(1).iter.len())) == to_integer(chunk_len / 4u64) - to_integer(loop(1).iter.len()); to_integer(loop(1).iter.len()) + iterations == to_integer(chunk_len / 4u64); };
        have (chunk_len / 4u64 - loop(1).iter.len()) < chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64).len() by solve() using { chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64).len() == chunk_len / 4u64; 0u64 < loop(1).iter.len(); loop(1).iter.len() <= chunk_len / 4u64; };
        have loop(1).iter.nth(0u64) == chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64).nth((chunk_len / 4u64 - loop(1).iter.len())) by {
         apply(chunks_exact::nth_after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64), iterations, 0u64, (chunk_len / 4u64 - loop(1).iter.len())));
         solve();
        }
        have loop(1).iter.nth(0u64).len() == 4u64 by {
         apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64, (chunk_len / 4u64 - loop(1).iter.len())));
         solve();
        }
        have loop(1).iter.after_next() == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64), iterations + 1) by {
         apply(chunks_exact::after_next_after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64), iterations));
         solve();
        }
        have loop(1).iter.after_next().len() == loop(1).iter.len() - 1u64 by {
         apply(chunks_exact::len_after_next(loop(1).iter));
        }
        apply(adler_chunk_bytes_next_4(loop(1).iter.len(), chunk_len));
        have chunk_len % 4u64 == 0u64 by { rewrite(chunk_len, 22208u64); normalize(); }
        apply(adler_chunk_bytes_offset_whole_4(loop(1).iter.len(), chunk_len));
        have 4u64 <= adler_chunk_bytes(loop(1).iter.len(), 4u64);
        have 4 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) by {
         have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 2147483647u64 by solve() using { adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64; };
         apply(adler_bounded_count_lower(adler_chunk_bytes(loop(1).iter.len(), 4u64), 4));
         known();
        }
        have 4u64 <= adler_chunk_bytes(loop(1).iter.len(), 4u64);
        have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); };
        have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(bytes.len()) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len()); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer(bytes.len()) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(bytes.len()); };
        have to_integer(4u64) <= to_integer(bytes.len() - ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(bytes.len()); 4u64 <= adler_chunk_bytes(loop(1).iter.len(), 4u64); };
        // The first fact about the chunk's pointer is its offset from `bytes`: the helper call
        // below reads the chunk through the input's view, and the view is found by that fact.
        have loop(1).iter.nth(0u64).as_ptr() == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by {
         have loop(1).iter.nth(0u64).as_ptr() == chunk + (chunk_len / 4u64 - loop(1).iter.len()) * 4u64 by {
          apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64, (chunk_len / 4u64 - loop(1).iter.len())));
          solve();
         }
         have loop(1).iter.nth(0u64).as_ptr() == chunk + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by {
          rewrite(to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer((chunk_len / 4u64 - loop(1).iter.len()) * 4u64));
          known();
         }
         apply(integer::uint64_subtract_to_integer(chunk_len, adler_chunk_bytes(loop(1).iter.len(), 4u64)));
         apply(integer::uint64_subtract_to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64), adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
         apply(integer::uint64_subtract_to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), 22208u64));
         apply(integer::uint64_subtract_to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), adler_chunk_bytes(loop(1).iter.len(), 4u64)));
         have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by solve() using { to_integer(chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(chunk_len) - to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - to_integer(22208u64); to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); chunk_len == 22208u64; };
         have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= 18446744073709551615 by solve() using { to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer(bytes.len()); };
         apply(integer::uint64_add_to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64), (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))));
         have chunk + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by { rewrite(chunk, bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)); solve() using { to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= 18446744073709551615; to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))); }; }
         have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by solve() using { to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
         rewrite(to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))));
         solve() using { loop(1).iter.nth(0u64).as_ptr() == chunk + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)); chunk + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        }
        apply(integer::uint64_subtract_to_integer(chunk_len, adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        apply(integer::uint64_subtract_to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64), adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
        apply(integer::uint64_subtract_to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), 22208u64));
        apply(integer::uint64_subtract_to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by solve() using { to_integer(chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(chunk_len) - to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - to_integer(22208u64); to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); chunk_len == 22208u64; };
        have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= 18446744073709551615 by solve() using { to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer(bytes.len()); };
        apply(integer::uint64_add_to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64), (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))));
        have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by solve() using { to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        apply(integer::uint64_subtract_to_integer(bytes.len(), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))));
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()) by solve() using { to_integer(4u64) <= to_integer(bytes.len() - ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer(bytes.len() - ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(bytes.len()) - to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) < to_integer(bytes.len()) by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(3u64) <= 18446744073709551615 by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        apply(integer::uint64_add_to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)), 3u64));
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) + 3u64) < to_integer(bytes.len()) by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) + 3u64) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(3u64); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) < to_integer(bytes.len()) by solve() using { to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) < to_integer(bytes.len()); };
        have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 3 < to_integer(bytes.len()) by solve() using { to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        // The inner loop views the aligned prefix only: bound the chunk inside it.
        have to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64)) by normalize();
        apply(integer::uint64_subtract_to_integer((bytes.len() - bytes.len() % 4u64), (bytes.len() - bytes.len() % 4u64) % 22208u64));
        have 0 <= to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64);
        have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)) by solve() using { to_integer((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) == to_integer((bytes.len() - bytes.len() % 4u64)) - to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64); 0 <= to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64); };
        have 0 <= to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer((bytes.len() - bytes.len() % 4u64)) by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) - to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)); 4u64 <= adler_chunk_bytes(loop(1).iter.len(), 4u64); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)); 0 <= to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) < to_integer((bytes.len() - bytes.len() % 4u64)) by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer((bytes.len() - bytes.len() % 4u64)); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) + 3u64) < to_integer((bytes.len() - bytes.len() % 4u64)) by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) + 3u64) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(3u64); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer((bytes.len() - bytes.len() % 4u64)); };
        // The same chunk starts `chunk_len - remaining` bytes into the batch, where the old cursor stood.
        have loop(1).iter.nth(0u64).as_ptr() == chunk + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by {
         have loop(1).iter.nth(0u64).as_ptr() == chunk + (chunk_len / 4u64 - loop(1).iter.len()) * 4u64 by {
          apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64, (chunk_len / 4u64 - loop(1).iter.len())));
          solve();
         }
         rewrite(to_integer(chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)), to_integer((chunk_len / 4u64 - loop(1).iter.len()) * 4u64));
         known();
        }
        have chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64 by solve() using { adler_chunk_bytes(loop(1).iter.len(), 4u64) <= chunk_len; chunk_len == 22208u64; };
        apply(adler_count_byte_pointer(chunk, chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        have chunk_len <= 22208u64 by solve() using { chunk_len == 22208u64; };
        apply(adler_count_step(chunk_len, adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        have ((chunk_len as u32) as i32) == 22208 by { rewrite(chunk_len, 22208u64); normalize(); }
        have to_integer((((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) as uint32) as int32)) == to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by {
         rewrite(to_integer((((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) as uint32) as int32)), to_integer(((chunk_len as uint32) as int32) - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
         rewrite(((chunk_len as uint32) as int32), 22208);
         normalize();
        }
        have loop(1).iter.nth(0u64).as_ptr() == (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by {
         rewrite(to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), to_integer((((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) as uint32) as int32)));
         solve() using { loop(1).iter.nth(0u64).as_ptr() == chunk + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)); chunk + (chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == chunk + (((chunk_len - adler_chunk_bytes(loop(1).iter.len(), 4u64)) as uint32) as int32); };
        }
        mark lane_head;
        have at(lane_head, loop(1).iter.nth(0u64).as_ptr()) == at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have at(lane_head, loop(1).iter.nth(0u64).len()) == 4u64;
        have 0u64 < at(lane_head, loop(1).iter.len());
        have to_integer(adler_chunk_bytes(at(lane_head, loop(1).iter.len()) - 1u64, 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64);
        have at(lane_head, loop(1).iter.after_next()) == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64), iterations + 1);
        have to_integer(at(lane_head, loop(1).iter.len())) + iterations == to_integer(chunk_len / 4u64);
        have at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) % 4 == 0;
        have at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208;
        have 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32));
        have 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32));
        have 22208 <= 22208 by solve() using { 22208 <= 22208; };
        have at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) == at(loop(1).entry, chunk) + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have 0 <= to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { 0 <= 22208; 22208 <= 22208; 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; };
        have to_integer((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) + 4) <= 22208 by solve() using { 0 <= 22208; 22208 <= 22208; 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; };
        step_until(assignment(__rust_mir_43, 0)); step();
        have __rust_mir_43 == at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        step_until(assignment(__rust_mir_43_len, 0)); step();
        have __rust_mir_43_len == 4u64;
        have loop(1).iter == at(lane_head, loop(1).iter.after_next());
        have loop(1).iter.len() == at(lane_head, loop(1).iter.len()) - 1u64;
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64) by { rewrite(loop(1).iter.len(), at(lane_head, loop(1).iter.len()) - 1u64); known(); }
        have 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= 22208u64;
        apply(integer::uint64_subtract_to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)), 4u64));
        have adler_chunk_bytes(loop(1).iter.len(), 4u64) == at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64 by solve() using { to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64); to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) - to_integer(4u64); };
        apply(adler_count_lane_step(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))));
        have __rust_mir_43 == at(loop(1).entry, chunk) + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(__rust_mir_43, at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))))); known(); }
        have __rust_mir_43 == chunk + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4);
        have 22208 == 22208 by solve() using { chunk_len == 22208u64; };
        have 0 <= 22208 by known();
        have 22208 <= 22208 by known();
        have 22208 <= 22208 by solve() using { 22208 == 22208; 22208 <= 22208; };
        have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using {
          to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4);
          4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32));
          at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208;
         };
        have 0 <= to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) by { rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); known(); }
        have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) <= 22208 by solve() using { 22208 <= 22208; 0 <= 22208; 22208 <= 22208; to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 0 <= 22208; 22208 <= 22208; 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; };
        have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) <= to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by solve() using { 22208 == 22208; to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 0 <= 22208; 22208 <= 22208; 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 0 <= to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)); to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) <= 22208; 0 <= 22208; 22208 <= 22208; };
        have __rust_mir_43 == chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4);
        have to_integer((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) <= 22204 by solve() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; };
        // The helper reads the chunk through the input's view: place its pointer in `bytes`.
        step_until(assignment(__rust_mir_42, 0));
        have __rust_checked_2 == __rust_mir_43;
        have at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        have __rust_checked_2 == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) by solve() using { __rust_checked_2 == __rust_mir_43; __rust_mir_43 == at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) <= to_integer(bytes.len());
        have to_integer(4u64) <= to_integer(bytes.len() - ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))));
        apply(integer::uint64_subtract_to_integer(bytes.len(), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))));
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615 by solve() using { to_integer(4u64) <= to_integer(bytes.len() - ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); to_integer(bytes.len() - ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) == to_integer(bytes.len()) - to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); };
        apply(integer::uint64_add_to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), 4u64));
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) <= to_integer(bytes.len()) by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64); to_integer(4u64) <= to_integer(bytes.len() - ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); to_integer(bytes.len() - ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) == to_integer(bytes.len()) - to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); };
        have __rust_mir_43 == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) by solve() using { __rust_checked_2 == __rust_mir_43; __rust_checked_2 == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) < to_integer(bytes.len()) by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) <= to_integer(bytes.len()); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(3u64) <= 18446744073709551615 by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615; };
        apply(integer::uint64_add_to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), 3u64));
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 3u64) < to_integer(bytes.len()) by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 3u64) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(3u64); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) <= to_integer(bytes.len()); };
        mark before_from;
        // The helper call is one simple step of its own.
        step();
        step_until(assignment(__rust_mir_45, 0));
        have to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4);
        mark vector_a;
        // Connect the actual constructor bytes to the input at the uint64 cursor.
        // Prove machine equality before rewriting an Integer observation;
        // pointer rewriting inside an observation exposes different retained_states.
        have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) <= 22204 by { rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); solve() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; }; }
        have at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        have to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64)); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + 4 <= 18446744073709551615 by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64); };
        have at(vector_a, __rust_mir_43) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) by solve() using { __rust_mir_43 == at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        have at(before_from, __rust_checked_2) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) by solve() using { __rust_checked_2 == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        have to_integer(at(vector_a, __rust_mir_42.0[0])) == at(before_from, to_integer((__rust_checked_2[0] as i32))) by normalize() using { to_integer(__rust_mir_42.0[0]) == at(before_from, to_integer((__rust_checked_2[0] as i32))); };
        have at(before_from, (__rust_checked_2[0] as i32)) == at(before_from, ((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32)) by {
         rewrite(at(before_from, __rust_checked_2), bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); solve();
        }
        have to_integer(at(vector_a, __rust_mir_42.0[0])) == at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_42.0[0])), at(before_from, to_integer((__rust_checked_2[0] as i32))));
         rewrite(at(before_from, (__rust_checked_2[0] as i32)), at(before_from, ((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32)));
         normalize();
        }
        have at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32))) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32))) by solve();
        have to_integer(at(vector_a, __rust_mir_42.0[0])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_42.0[0])), at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32)))); known();
        }
        have to_integer(at(vector_a, __rust_mir_42.0[1])) == at(before_from, to_integer((__rust_checked_2[1] as i32))) by normalize() using { to_integer(__rust_mir_42.0[1]) == at(before_from, to_integer((__rust_checked_2[1] as i32))); };
        have at(before_from, (__rust_checked_2[1] as i32)) == at(before_from, ((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32)) by {
         rewrite(at(before_from, __rust_checked_2), bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); solve();
        }
        have to_integer(at(vector_a, __rust_mir_42.0[1])) == at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_42.0[1])), at(before_from, to_integer((__rust_checked_2[1] as i32))));
         rewrite(at(before_from, (__rust_checked_2[1] as i32)), at(before_from, ((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32)));
         normalize();
        }
        have at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32))) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32))) by solve();
        have to_integer(at(vector_a, __rust_mir_42.0[1])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_42.0[1])), at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32)))); known();
        }
        have to_integer(at(vector_a, __rust_mir_42.0[2])) == at(before_from, to_integer((__rust_checked_2[2] as i32))) by normalize() using { to_integer(__rust_mir_42.0[2]) == at(before_from, to_integer((__rust_checked_2[2] as i32))); };
        have at(before_from, (__rust_checked_2[2] as i32)) == at(before_from, ((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32)) by {
         rewrite(at(before_from, __rust_checked_2), bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); solve();
        }
        have to_integer(at(vector_a, __rust_mir_42.0[2])) == at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_42.0[2])), at(before_from, to_integer((__rust_checked_2[2] as i32))));
         rewrite(at(before_from, (__rust_checked_2[2] as i32)), at(before_from, ((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32)));
         normalize();
        }
        have at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32))) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32))) by solve();
        have to_integer(at(vector_a, __rust_mir_42.0[2])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_42.0[2])), at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32)))); known();
        }
        have to_integer(at(vector_a, __rust_mir_42.0[3])) == at(before_from, to_integer((__rust_checked_2[3] as i32))) by normalize() using { to_integer(__rust_mir_42.0[3]) == at(before_from, to_integer((__rust_checked_2[3] as i32))); };
        have at(before_from, (__rust_checked_2[3] as i32)) == at(before_from, ((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32)) by {
         rewrite(at(before_from, __rust_checked_2), bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); solve();
        }
        have to_integer(at(vector_a, __rust_mir_42.0[3])) == at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_42.0[3])), at(before_from, to_integer((__rust_checked_2[3] as i32))));
         rewrite(at(before_from, (__rust_checked_2[3] as i32)), at(before_from, ((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32)));
         normalize();
        }
        have at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32))) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32))) by solve();
        have to_integer(at(vector_a, __rust_mir_42.0[3])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_42.0[3])), at(before_from, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32)))); known();
        }
        have 0 <= to_integer(at(vector_a, a_vec.0[0]));
        have 0 <= to_integer(at(vector_a, b_vec.0[0]));
        have to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, __rust_mir_42.0[0]));
        have to_integer(at(vector_a, __rust_mir_42.0[0])) <= 255;
        apply(adler_lane_iterator_add_contracts(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_42.0[0]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[0])); to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[0])); to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[0])); to_integer(at(vector_a, __rust_mir_42.0[0])) <= 255; };
        apply(adler_lane_iterator_native_preservation(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_42.0[0]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[0])); to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[0])); to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[0])); to_integer(at(vector_a, __rust_mir_42.0[0])) <= 255; };
        have 0 <= to_integer(at(vector_a, a_vec.0[1]));
        have 0 <= to_integer(at(vector_a, b_vec.0[1]));
        have to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, __rust_mir_42.0[1]));
        have to_integer(at(vector_a, __rust_mir_42.0[1])) <= 255;
        apply(adler_lane_iterator_add_contracts(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_42.0[1]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[1])); to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[1])); to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[1])); to_integer(at(vector_a, __rust_mir_42.0[1])) <= 255; };
        apply(adler_lane_iterator_native_preservation(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_42.0[1]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[1])); to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[1])); to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[1])); to_integer(at(vector_a, __rust_mir_42.0[1])) <= 255; };
        have 0 <= to_integer(at(vector_a, a_vec.0[2]));
        have 0 <= to_integer(at(vector_a, b_vec.0[2]));
        have to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, __rust_mir_42.0[2]));
        have to_integer(at(vector_a, __rust_mir_42.0[2])) <= 255;
        apply(adler_lane_iterator_add_contracts(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_42.0[2]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[2])); to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[2])); to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[2])); to_integer(at(vector_a, __rust_mir_42.0[2])) <= 255; };
        apply(adler_lane_iterator_native_preservation(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_42.0[2]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[2])); to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[2])); to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[2])); to_integer(at(vector_a, __rust_mir_42.0[2])) <= 255; };
        have 0 <= to_integer(at(vector_a, a_vec.0[3]));
        have 0 <= to_integer(at(vector_a, b_vec.0[3]));
        have to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, __rust_mir_42.0[3]));
        have to_integer(at(vector_a, __rust_mir_42.0[3])) <= 255;
        apply(adler_lane_iterator_add_contracts(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_42.0[3]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[3])); to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[3])); to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[3])); to_integer(at(vector_a, __rust_mir_42.0[3])) <= 255; };
        apply(adler_lane_iterator_native_preservation(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_42.0[3]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[3])); to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[3])); to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[3])); to_integer(at(vector_a, __rust_mir_42.0[3])) <= 255; };
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(vector_a, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(a)) by { solve(); }
        have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) by { have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); }; rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); solve(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[0]), at(vector_a, __rust_mir_42.0[0]))) using { to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295; };
        have to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])), to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))); known(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[1]), at(vector_a, __rust_mir_42.0[1]))) using { to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295; };
        have to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))); known(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[2]), at(vector_a, __rust_mir_42.0[2]))) using { to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295; };
        have to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))); known(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[3]), at(vector_a, __rust_mir_42.0[3]))) using { to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295; };
        have to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))); known(); }
        apply(adler_native_deferred_b_step((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_42.0[0]), at(vector_a, __rust_mir_42.0[1]), at(vector_a, __rust_mir_42.0[2]), at(vector_a, __rust_mir_42.0[3]))) using { 0 <= to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)); to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) <= 22204; 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295; to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3]))) <= 4294967295; };
        apply(adler_nonnegative_deferred_b_step((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_42.0[0]), at(vector_a, __rust_mir_42.0[1]), at(vector_a, __rust_mir_42.0[2]), at(vector_a, __rust_mir_42.0[3]))) using { 0 <= to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)); to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) <= 22204; 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295; to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3]))) <= 4294967295; };
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b_u64(at(vector_a, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(at(vector_a, a)), old(to_integer((self.b as u32)))) by { have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); }; rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); solve(); }
        apply(adler_native_deferred_b_prefix_step_u64(at(vector_a, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4), to_integer(a), old(to_integer((self.b as u32))), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_42.0[0]), at(vector_a, __rust_mir_42.0[1]), at(vector_a, __rust_mir_42.0[2]), at(vector_a, __rust_mir_42.0[3]))) using {
         to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + 4 <= 18446744073709551615;
         0 <= to_integer(a); to_integer(a) <= 65520;
         truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(vector_a, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(a));
         to_integer(at(vector_a, __rust_mir_42.0[0])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32)));
         to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_42.0[1])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32)));
         to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_42.0[2])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32)));
         to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_42.0[3])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32)));
         to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295;
         0 <= to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)); to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) <= 22204; 0 <= old(to_integer((self.b as u32))); 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b_u64(at(vector_a, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(at(vector_a, a)), old(to_integer((self.b as u32)))); to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3]))) <= 4294967295;
        };
        apply(adler_native_four_lane_a_prefix_step_u64(at(vector_a, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(a), to_integer(a), at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, __rust_mir_42.0[0]), at(vector_a, __rust_mir_42.0[1]), at(vector_a, __rust_mir_42.0[2]), at(vector_a, __rust_mir_42.0[3]))) using {
         to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + 4 <= 18446744073709551615;
         0 <= to_integer(a); to_integer(a) <= 65520;
         truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(vector_a, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(a));
         to_integer(at(vector_a, __rust_mir_42.0[0])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32)));
         to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_42.0[1])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32)));
         to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_42.0[2])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32)));
         to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_42.0[3])) == at(vector_a, to_integer(((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32)));
         to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295;
        };
        have to_integer(a_vec.0[0]) + to_integer(__rust_mir_42.0[0]) <= 4294967295 by solve() using { to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295; };
        have to_integer(a_vec.0[1]) + to_integer(__rust_mir_42.0[1]) <= 4294967295 by solve() using { to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295; };
        have to_integer(a_vec.0[2]) + to_integer(__rust_mir_42.0[2]) <= 4294967295 by solve() using { to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295; };
        have to_integer(a_vec.0[3]) + to_integer(__rust_mir_42.0[3]) <= 4294967295 by solve() using { to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295; };
        step_until(assignment(__rust_mir_48, 0));
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]));
        have b_vec.0[0] == at(vector_a, b_vec.0[0]);
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])) by solve() using { b_vec.0[0] == at(vector_a, b_vec.0[0]); };
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])) by solve() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])); };
        have to_integer(b_vec.0[0]) + to_integer(a_vec.0[0]) <= 4294967295 by solve() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])); to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])); to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])) <= 4294967295; };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]));
        have b_vec.0[1] == at(vector_a, b_vec.0[1]);
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])) by solve() using { b_vec.0[1] == at(vector_a, b_vec.0[1]); };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); };
        have to_integer(b_vec.0[1]) + to_integer(a_vec.0[1]) <= 4294967295 by solve() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) <= 4294967295; };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]));
        have b_vec.0[2] == at(vector_a, b_vec.0[2]);
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])) by solve() using { b_vec.0[2] == at(vector_a, b_vec.0[2]); };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); };
        have to_integer(b_vec.0[2]) + to_integer(a_vec.0[2]) <= 4294967295 by solve() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) <= 4294967295; };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]));
        have b_vec.0[3] == at(vector_a, b_vec.0[3]);
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])) by solve() using { b_vec.0[3] == at(vector_a, b_vec.0[3]); };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); };
        have to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]) <= 4294967295 by solve() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) <= 4294967295; };
        mark vector_b;
        step_until(back_edge());
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]));
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])));
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])) by solve() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))) by solve() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]));
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])));
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))) by solve() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]));
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])));
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))) by solve() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]));
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])));
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))) by solve() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); };
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208 by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; };
        have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208 by known();
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by { rewrite(to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); normalize() using { at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) % 4 == 0; 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; }; }
        have to_integer((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) + 4) == to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; };
        have 0 <= to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; };
        have to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) <= 22204 by solve() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; };
        have 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by solve() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); };
        have defined(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have (at(loop(1).entry, chunk) + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) + 4 == at(loop(1).entry, chunk) + ((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) + 4) by apply(adler_bounded_pointer_association(at(loop(1).entry, chunk), 22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) using { defined(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); 0 <= to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) <= 22204; };
        have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == at(loop(1).entry, chunk) + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by solve() using { chunk == at(loop(1).entry, chunk); };
        // The cursor term advanced by four bytes with the count.
        have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) + 4 by { rewrite((chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))), at(loop(1).entry, chunk) + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); rewrite(at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))), at(loop(1).entry, chunk) + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); rewrite((at(loop(1).entry, chunk) + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) + 4, at(loop(1).entry, chunk) + ((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) + 4)); rewrite(to_integer((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) + 4), to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); normalize() using {}; }
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) < at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; };
        have chunk_len == 22208u64 by known();
        have chunk == at(loop(1).entry, chunk) by known();
        have bytes == old(bytes) by known();
        have bytes.len() == old(bytes.len()) by known();
        have 22208u64 == 22208u64 by known();
        have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(loop(1).entry, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by known();
        have (bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) == at(loop(1).entry, (bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) by known();
        have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64 by known();
        have remainder_len == bytes.len() % 4u64 by known();
        have chunk_len == 22208u64 by known();
        have a <= 65520u32 by known();
        have b <= 65520u32 by known();
        have 4u64 == 4u64 by known();
        have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208 by known();
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by known();
        have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == at(loop(1).entry, chunk) + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by known();
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64);
        have 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= 22208u64;
        have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64 by solve() using {
         to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64);
         4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64));
         at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= 22208u64;
        };
        have adler_chunk_bytes(loop(1).iter.len(), 4u64) < at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) by solve() using {
         to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64);
         4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64));
         at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= 22208u64;
        };
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64);
        have 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) by known();
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) by solve() using { to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64) by solve() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)); };
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615 by solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64); };
        apply(integer::uint64_add_to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), 4u64));
        have __rust_mir_43 + 4 == bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) by { rewrite(__rust_mir_43, bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); solve() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615; to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64); }; }
        have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == __rust_mir_43 + 4 by { rewrite(__rust_mir_43, at(lane_head, (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))))); known(); }
        have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) by solve() using { to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer(bytes.len() - bytes.len() % 4u64); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); };
        have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by { rewrite(to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64)); solve() using { (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == __rust_mir_43 + 4; __rust_mir_43 + 4 == bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64); }; }
        have defined(22208 - (((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by solve() using { 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32); ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208; };
        // Retain the exact A transition at the actual inner back edge.
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22204 by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; };
        apply(adler_full_batch_within_advance(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) using { 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32); ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22204; };
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a)) by {
         rewrite(to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64));
         rewrite(to_integer(a_vec.0[0]), to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])));
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])));
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])));
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])));
         solve();
        }
        have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by { rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4), to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); normalize(); }
        have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by {
         have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by solve() using { to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4); };
         rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))), to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4));
         have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); };
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])));
         have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); };
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])));
         have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); };
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])));
         have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))) by solve() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))); };
         rewrite(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))));
         have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))) by solve() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))); };
         rewrite(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))));
         have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))) by solve() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))); };
         rewrite(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))));
         have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))) by solve() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))); };
         rewrite(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))));
         solve();
        }
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32)))) by {
         rewrite(to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64));
         have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by solve() using { to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4); };
         rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))), to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4));
         have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); };
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])));
         have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); };
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])));
         have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); };
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])));
         have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))) by solve() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))); };
         rewrite(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))));
         have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))) by solve() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))); };
         rewrite(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))));
         have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))) by solve() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))); };
         rewrite(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))));
         have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))) by solve() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))); };
         rewrite(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))));
         solve();
        }
        // The invariants at the back edge, one pass further on.
        have loop(0).iter.len() == at(loop(1).entry, loop(0).iter.len());
        have loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), (to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len())));
        have loop(1).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64), iterations + 1);
        have to_integer(loop(1).iter.len()) + (iterations + 1) == to_integer(chunk_len / 4u64) by solve() using { loop(1).iter.len() == at(lane_head, loop(1).iter.len()) - 1u64; 0u64 < at(lane_head, loop(1).iter.len()); to_integer(at(lane_head, loop(1).iter.len())) + iterations == to_integer(chunk_len / 4u64); };
        have loop(1).iter.len() <= chunk_len / 4u64;
        // Every invariant at the back edge.
        have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64;
        have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
        have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len());
        have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
        have chunk == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64);
        have to_integer(22208u64) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) <= to_integer(bytes.len());
        have to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64));
        have chunk_len == 22208u64;
        have chunk == at(loop(1).entry, chunk);
        have bytes == old(bytes);
        have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
        have bytes.len() == old(bytes.len());
        have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(loop(1).entry, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
        have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
        have to_integer(__rust_checked_93) == to_integer(bytes.len() - bytes.len() % 4u64);
        have __rust_checked_94 == 22208u64;
        have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
        have remainder_len == bytes.len() % 4u64;
        have a <= 65520u32;
        have b <= 65520u32;
        have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208;
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a));
        have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
        have 0 <= old(to_integer((self.b as u32)));
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
        have loop(0).iter.len() == at(loop(1).entry, loop(0).iter.len());
        have loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), (to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len())));
        have loop(1).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64), (iterations + 1));
        have to_integer(loop(1).iter.len()) + (iterations + 1) == to_integer(chunk_len / 4u64);
        // The ranking members: the measure is read at the pass entry, before the header ran.
        have at(lane_head, loop(1).iter.len()) == at(inner_pass, loop(1).iter.len());
        have loop(1).iter.len() < at(lane_head, loop(1).iter.len()) by solve() using { loop(1).iter.len() == at(lane_head, loop(1).iter.len()) - 1u64; 0u64 < at(lane_head, loop(1).iter.len()); };
        have loop(1).iter.len() < at(inner_pass, loop(1).iter.len()) by solve() using { loop(1).iter.len() < at(lane_head, loop(1).iter.len()); at(lane_head, loop(1).iter.len()) == at(inner_pass, loop(1).iter.len()); };
       } else {
        // No chunk is left: the header test fails and the loop leaves by `break`.
        step();
        have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64;
        have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
        have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len());
        have (chunk + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
        have chunk == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64);
        have to_integer(22208u64) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) <= to_integer(bytes.len());
        have to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64));
        have chunk_len == 22208u64;
        have chunk == at(loop(1).entry, chunk);
        have bytes == old(bytes);
        have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
        have bytes.len() == old(bytes.len());
        have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(loop(1).entry, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
        have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
        have to_integer(__rust_checked_93) == to_integer(bytes.len() - bytes.len() % 4u64);
        have __rust_checked_94 == 22208u64;
        have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
        have remainder_len == bytes.len() % 4u64;
        have a <= 65520u32;
        have b <= 65520u32;
        have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208;
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a));
        have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
        have 0 <= old(to_integer((self.b as u32)));
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
        have loop(0).iter.len() == at(loop(1).entry, loop(0).iter.len());
        have loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), (to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len())));
        have loop(1).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 4u64), iterations);
        have to_integer(loop(1).iter.len()) + iterations == to_integer(chunk_len / 4u64);
        step();
       }
      }
     }
      have loop(1).iter.len() == 0u64;
      apply(adler_chunk_bytes_none(4u64));
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) == 0u64 by { rewrite(loop(1).iter.len(), 0u64); known(); }
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) < 4u64 by solve() using { adler_chunk_bytes(loop(1).iter.len(), 4u64) == 0u64; };
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 2147483647u64 by solve() using { adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64; };
      apply(adler_bounded_count(adler_chunk_bytes(loop(1).iter.len(), 4u64)));
      have to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) < to_integer(4) by solve() using {
       to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64));
       to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) < to_integer(4u64);
      };
      have to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= to_integer(3) by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) < to_integer(4); };
      have (((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 3;
      have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) < 4 by solve() using { ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 3; };
      have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) by normalize() using { 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32); ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) < 4; };
      have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) == 0 by solve() using { ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0; ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32); };
      have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == 0 by solve() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) == 0; };
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) == 0u64;
      have to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by { rewrite(adler_chunk_bytes(loop(1).iter.len(), 4u64), 0u64); normalize(); }
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a)) by { rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); solve(); }
      apply(adler_complete_full_batch_position(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) using { ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) == 0; };
      have 0 <= adler_lane_b(to_integer(b) + 22208 * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(22208, to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); known(); }
      have truncating_remainder(adler_lane_b(to_integer(b) + 22208 * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(22208, to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); solve(); }
      mark full_lane_prefix;
      have truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(full_lane_prefix, bytes), ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(at(full_lane_prefix, a))) by solve();
      have 0 <= to_integer((at(full_lane_prefix, a)));
      have to_integer((at(full_lane_prefix, a))) <= 4294967295;
      have 0 <= to_integer((at(full_lane_prefix, a_vec.0[0])));
      have to_integer((at(full_lane_prefix, a_vec.0[0]))) <= 4294967295;
      have 0 <= to_integer((at(full_lane_prefix, a_vec.0[1])));
      have to_integer((at(full_lane_prefix, a_vec.0[1]))) <= 4294967295;
      have 0 <= to_integer((at(full_lane_prefix, a_vec.0[2])));
      have to_integer((at(full_lane_prefix, a_vec.0[2]))) <= 4294967295;
      have 0 <= to_integer((at(full_lane_prefix, a_vec.0[3])));
      have to_integer((at(full_lane_prefix, a_vec.0[3]))) <= 4294967295;
      apply(adler_lane_a_reduction(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])))) using { 0 <= to_integer(at(full_lane_prefix, a)); 0 <= to_integer(at(full_lane_prefix, a_vec.0[0])); 0 <= to_integer(at(full_lane_prefix, a_vec.0[1])); 0 <= to_integer(at(full_lane_prefix, a_vec.0[2])); 0 <= to_integer(at(full_lane_prefix, a_vec.0[3])); };
      have truncating_remainder(adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))), 65521) == adler_spec_b_u64(at(full_lane_prefix, bytes), ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(at(full_lane_prefix, a)), old(to_integer((self.b as u32)))) by solve();
      // The deferred scalar seed and all lane observations are still exact.
      have 0 <= to_integer((at(full_lane_prefix, b)));
      have to_integer((at(full_lane_prefix, b))) <= 4294967295;
      have 0 <= to_integer((at(full_lane_prefix, b_vec.0[0])));
      have to_integer((at(full_lane_prefix, b_vec.0[0]))) <= 4294967295;
      have 0 <= to_integer((at(full_lane_prefix, b_vec.0[1])));
      have to_integer((at(full_lane_prefix, b_vec.0[1]))) <= 4294967295;
      have 0 <= to_integer((at(full_lane_prefix, b_vec.0[2])));
      have to_integer((at(full_lane_prefix, b_vec.0[2]))) <= 4294967295;
      have 0 <= to_integer((at(full_lane_prefix, b_vec.0[3])));
      have to_integer((at(full_lane_prefix, b_vec.0[3]))) <= 4294967295;
      have 0 <= to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by solve() using { 0 <= to_integer(at(full_lane_prefix, b)); 0 <= to_integer(at(full_lane_prefix, a)); };
      have 0 <= adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))) by solve();
      apply(adler_lane_b_reduction(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3])))) using { 0 <= to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)); 0 <= to_integer(at(full_lane_prefix, a_vec.0[1])); 0 <= to_integer(at(full_lane_prefix, a_vec.0[2])); 0 <= to_integer(at(full_lane_prefix, a_vec.0[3])); 0 <= to_integer(at(full_lane_prefix, b_vec.0[0])); 0 <= to_integer(at(full_lane_prefix, b_vec.0[1])); 0 <= to_integer(at(full_lane_prefix, b_vec.0[2])); 0 <= to_integer(at(full_lane_prefix, b_vec.0[3])); 0 <= adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))); };
      step_until(assignment(__rust_mir_52, 0)); step();
      have __rust_mir_51 == 22208u32;
      have __rust_mir_52 <= 65520u32 by solve() using { a <= 65520u32; };
      have to_integer(__rust_mir_51) * to_integer(__rust_mir_52) <= 1455068160 by {
       rewrite(__rust_mir_51, 22208u32);
       solve() using { to_integer(__rust_mir_52) <= 65520; };
      }
      have to_integer(__rust_mir_51) * to_integer(__rust_mir_52) <= 4294967295 by solve() using { to_integer(__rust_mir_51) * to_integer(__rust_mir_52) <= 1455068160; };
      apply(integer::uint32_multiply_guard_by_integer_bound(__rust_mir_51, __rust_mir_52)) using { to_integer(__rust_mir_51) * to_integer(__rust_mir_52) <= 4294967295; };
      apply(integer::uint32_multiply_to_integer(__rust_mir_51, __rust_mir_52)) using { __rust_mir_52 == 0u32 or __rust_mir_51 <= 4294967295u32 / __rust_mir_52; };
      mark full_product;
      have to_integer(at(full_product, __rust_mir_51)) * to_integer(at(full_product, __rust_mir_52)) <= 1455068160 by solve() using { to_integer(__rust_mir_51) * to_integer(__rust_mir_52) <= 1455068160; };
      have at(full_product, __rust_mir_52) == 0u32 or at(full_product, __rust_mir_51) <= 4294967295u32 / at(full_product, __rust_mir_52) by solve() using { __rust_mir_52 == 0u32 or __rust_mir_51 <= 4294967295u32 / __rust_mir_52; };
      apply(integer::uint32_multiply_to_integer(at(full_product, __rust_mir_51), at(full_product, __rust_mir_52))) using { at(full_product, __rust_mir_52) == 0u32 or at(full_product, __rust_mir_51) <= 4294967295u32 / at(full_product, __rust_mir_52); };
      if __rust_mir_52 == 0u32 {
       step_until(assignment(__rust_mir_50, 0)); step();
      } else {
       have __rust_mir_51 <= 4294967295u32 / __rust_mir_52 by { cases {
        __rust_mir_52 == 0u32 => { contradiction(not (__rust_mir_52 == 0u32)); }
        __rust_mir_51 <= 4294967295u32 / __rust_mir_52 => { known(); }
       } }
       step_until(assignment(__rust_mir_50, 0)); step();
      }
      have to_integer(__rust_mir_50) == to_integer(at(full_product, __rust_mir_51) * at(full_product, __rust_mir_52));
      have to_integer(__rust_mir_50) <= 1455068160 by {
       rewrite(to_integer(__rust_mir_50), to_integer(at(full_product, __rust_mir_51) * at(full_product, __rust_mir_52)));
       rewrite(to_integer(at(full_product, __rust_mir_51) * at(full_product, __rust_mir_52)), to_integer(at(full_product, __rust_mir_51)) * to_integer(at(full_product, __rust_mir_52)));
       known();
      }
      have to_integer(b) + to_integer(__rust_mir_50) <= 4294967295 by solve() using { to_integer(b) <= 65520; to_integer(__rust_mir_50) <= 1455068160; };
      have b <= 4294967295u32 - __rust_mir_50 by solve() using { to_integer(b) + to_integer(__rust_mir_50) <= 4294967295; };
      apply(integer::uint32_add_to_integer(b, __rust_mir_50));
      have to_integer(b + __rust_mir_50) == to_integer(b) + to_integer(__rust_mir_50);
      have at(full_product, __rust_mir_51) == 22208u32 by solve();
      have at(full_product, __rust_mir_52) == at(full_lane_prefix, a) by solve();
      have to_integer(__rust_mir_50) == 22208 * to_integer(at(full_lane_prefix, a)) by {
       rewrite(to_integer(__rust_mir_50), to_integer(at(full_product, __rust_mir_51) * at(full_product, __rust_mir_52)));
       rewrite(to_integer(at(full_product, __rust_mir_51) * at(full_product, __rust_mir_52)), to_integer(at(full_product, __rust_mir_51)) * to_integer(at(full_product, __rust_mir_52)));
       rewrite(at(full_product, __rust_mir_51), 22208u32);
       rewrite(at(full_product, __rust_mir_52), at(full_lane_prefix, a));
       normalize();
      }
      mark full_seed_add;
      have at(full_seed_add, b) == at(full_lane_prefix, b) by solve();
      have to_integer(at(full_seed_add, __rust_mir_50)) == 22208 * to_integer(at(full_lane_prefix, a)) by solve();
      have to_integer(at(full_seed_add, b) + at(full_seed_add, __rust_mir_50)) == to_integer(at(full_seed_add, b)) + to_integer(at(full_seed_add, __rust_mir_50)) by solve();
      step_until(assignment(__rust_mir_56, 0)); step();
      mark full_reduction_a;
      have at(full_reduction_a, a_vec.0[0]) == at(full_lane_prefix, a_vec.0[0]) by solve();
      have at(full_reduction_a, a_vec.0[1]) == at(full_lane_prefix, a_vec.0[1]) by solve();
      have at(full_reduction_a, a_vec.0[2]) == at(full_lane_prefix, a_vec.0[2]) by solve();
      have at(full_reduction_a, a_vec.0[3]) == at(full_lane_prefix, a_vec.0[3]) by solve();
      have to_integer(b) == to_integer(at(full_seed_add, b) + at(full_seed_add, __rust_mir_50)) by solve();
      have to_integer(b) == to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by {
       rewrite(to_integer(b), to_integer(at(full_seed_add, b) + at(full_seed_add, __rust_mir_50)));
       rewrite(to_integer(at(full_seed_add, b) + at(full_seed_add, __rust_mir_50)), to_integer(at(full_seed_add, b)) + to_integer(at(full_seed_add, __rust_mir_50)));
       rewrite(at(full_seed_add, b), at(full_lane_prefix, b));
       rewrite(to_integer(at(full_seed_add, __rust_mir_50)), 22208 * to_integer(at(full_lane_prefix, a)));
       normalize();
      }
      step_until(assignment(__rust_mir_58, 0)); step();
      mark full_reduction_b;
      have at(full_reduction_b, b_vec.0[0]) == at(full_lane_prefix, b_vec.0[0]) by solve();
      have at(full_reduction_b, b_vec.0[1]) == at(full_lane_prefix, b_vec.0[1]) by solve();
      have at(full_reduction_b, b_vec.0[2]) == at(full_lane_prefix, b_vec.0[2]) by solve();
      have at(full_reduction_b, b_vec.0[3]) == at(full_lane_prefix, b_vec.0[3]) by solve();
      have to_integer(at(full_reduction_b, b)) == to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by solve();
      step_until(assignment(b, 2));
      mark full_scalar_mod;
      have to_integer(a) == to_integer(at(full_lane_prefix, a));
      have __rust_checked_11 == 65521u32;
      have to_integer(__rust_checked_11) == 65521 by { rewrite(__rust_checked_11, 65521u32); normalize(); }
      have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[0])), to_integer(__rust_checked_11)) by solve();
      have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[0])), 65521) by {
       rewrite(at(full_lane_prefix, a_vec.0[0]), at(full_reduction_a, a_vec.0[0]));
       rewrite(65521, to_integer(__rust_checked_11));
       known();
      }
      have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[1])), to_integer(__rust_checked_11)) by solve();
      have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521) by {
       rewrite(at(full_lane_prefix, a_vec.0[1]), at(full_reduction_a, a_vec.0[1]));
       rewrite(65521, to_integer(__rust_checked_11));
       known();
      }
      have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[2])), to_integer(__rust_checked_11)) by solve();
      have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521) by {
       rewrite(at(full_lane_prefix, a_vec.0[2]), at(full_reduction_a, a_vec.0[2]));
       rewrite(65521, to_integer(__rust_checked_11));
       known();
      }
      have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[3])), to_integer(__rust_checked_11)) by solve();
      have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521) by {
       rewrite(at(full_lane_prefix, a_vec.0[3]), at(full_reduction_a, a_vec.0[3]));
       rewrite(65521, to_integer(__rust_checked_11));
       known();
      }
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521) by {
       rewrite(to_integer(a), to_integer(at(full_lane_prefix, a)));
       rewrite(to_integer(a_vec.0[0]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[0])), 65521));
       rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521));
       rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521));
       rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521));
       rewrite(truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521), truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[0])), 65521), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521)), 65521));
       normalize();
      }
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a)) by {
       rewrite(truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521), truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521));
       rewrite(to_integer(a), to_integer(at(full_lane_prefix, a)));
       solve();
      }
      have to_integer(at(full_scalar_mod, b)) == to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by solve();
      have __rust_checked_8 == 65521u32;
      have to_integer(__rust_checked_8) == 65521 by { rewrite(__rust_checked_8, 65521u32); normalize(); }
      have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[0])), to_integer(__rust_checked_8)) by solve();
      have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[0])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[0]), at(full_reduction_b, b_vec.0[0])); rewrite(65521, to_integer(__rust_checked_8)); known(); }
      have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[1])), to_integer(__rust_checked_8)) by solve();
      have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[1])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[1]), at(full_reduction_b, b_vec.0[1])); rewrite(65521, to_integer(__rust_checked_8)); known(); }
      have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[2])), to_integer(__rust_checked_8)) by solve();
      have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[2])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[2]), at(full_reduction_b, b_vec.0[2])); rewrite(65521, to_integer(__rust_checked_8)); known(); }
      have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[3])), to_integer(__rust_checked_8)) by solve();
      have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[3])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[3]), at(full_reduction_b, b_vec.0[3])); rewrite(65521, to_integer(__rust_checked_8)); known(); }
      step();
      have b == at(full_scalar_mod, b) % 65521u32;
      apply(integer::uint32_remainder_to_integer(at(full_scalar_mod, b), 65521u32)) using { 65521u32 != 0u32; };
      have to_integer(b) == truncating_remainder(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), 65521) by { rewrite(b, at(full_scalar_mod, b) % 65521u32); rewrite(to_integer(at(full_scalar_mod, b) % 65521u32), truncating_remainder(to_integer(at(full_scalar_mod, b)), to_integer(65521u32))); rewrite(to_integer(at(full_scalar_mod, b)), to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a))); normalize(); }
      have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == truncating_remainder(adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))), 65521) by {
       rewrite(to_integer(b), truncating_remainder(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), 65521));
       rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521));
       rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521));
       rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521));
       rewrite(to_integer(b_vec.0[0]), truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[0])), 65521));
       rewrite(to_integer(b_vec.0[1]), truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[1])), 65521));
       rewrite(to_integer(b_vec.0[2]), truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[2])), 65521));
       rewrite(to_integer(b_vec.0[3]), truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[3])), 65521));
       solve();
      }
      have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521), truncating_remainder(adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))), 65521)); solve(); }
      apply(integer::uint32_remainder_less_than_divisor(at(full_scalar_mod, b), 65521u32)) using { 65521u32 != 0u32; };
      have b < 65521u32 by { rewrite(b, at(full_scalar_mod, b) % 65521u32); known(); }
      have to_integer(b) <= 65520 by solve() using { to_integer(b) < 65521; };
      have __rust_checked_9 == 65521u32;
      have 65521u32 == __rust_checked_9 by solve() using { __rust_checked_9 == 65521u32; };
      have __rust_checked_12 == 65521u32;
      have 65521u32 == __rust_checked_12 by solve() using { __rust_checked_12 == 65521u32; };
      have a_vec.0[0] < __rust_checked_12;
      have a_vec.0[0] < 65521u32 by { rewrite(65521u32, __rust_checked_12); known(); }
      have to_integer(a_vec.0[0]) <= 65520 by solve() using { to_integer(a_vec.0[0]) < 65521; };
      have a_vec.0[1] < __rust_checked_12;
      have a_vec.0[1] < 65521u32 by { rewrite(65521u32, __rust_checked_12); known(); }
      have to_integer(a_vec.0[1]) <= 65520 by solve() using { to_integer(a_vec.0[1]) < 65521; };
      have a_vec.0[2] < __rust_checked_12;
      have a_vec.0[2] < 65521u32 by { rewrite(65521u32, __rust_checked_12); known(); }
      have to_integer(a_vec.0[2]) <= 65520 by solve() using { to_integer(a_vec.0[2]) < 65521; };
      have a_vec.0[3] < __rust_checked_12;
      have a_vec.0[3] < 65521u32 by { rewrite(65521u32, __rust_checked_12); known(); }
      have to_integer(a_vec.0[3]) <= 65520 by solve() using { to_integer(a_vec.0[3]) < 65521; };
      have b_vec.0[0] < __rust_checked_9;
      have b_vec.0[0] < 65521u32 by { rewrite(65521u32, __rust_checked_9); known(); }
      have to_integer(b_vec.0[0]) <= 65520 by solve() using { to_integer(b_vec.0[0]) < 65521; };
      have b_vec.0[1] < __rust_checked_9;
      have b_vec.0[1] < 65521u32 by { rewrite(65521u32, __rust_checked_9); known(); }
      have to_integer(b_vec.0[1]) <= 65520 by solve() using { to_integer(b_vec.0[1]) < 65521; };
      have b_vec.0[2] < __rust_checked_9;
      have b_vec.0[2] < 65521u32 by { rewrite(65521u32, __rust_checked_9); known(); }
      have to_integer(b_vec.0[2]) <= 65520 by solve() using { to_integer(b_vec.0[2]) < 65521; };
      have b_vec.0[3] < __rust_checked_9;
      have b_vec.0[3] < 65521u32 by { rewrite(65521u32, __rust_checked_9); known(); }
      have to_integer(b_vec.0[3]) <= 65520 by solve() using { to_integer(b_vec.0[3]) < 65521; };
      have adler_chunk_bytes(loop(0).iter.len(), 22208u64) < at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by solve() using { to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64); 22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)); };
      mark batch_reduced;
      have truncating_remainder(adler_lane_a(to_integer(at(batch_reduced, a)), to_integer(at(batch_reduced, a_vec.0[0])), to_integer(at(batch_reduced, a_vec.0[1])), to_integer(at(batch_reduced, a_vec.0[2])), to_integer(at(batch_reduced, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(batch_reduced, bytes), ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(at(batch_reduced, a))) by solve();
      have truncating_remainder(adler_lane_b(to_integer(at(batch_reduced, b)), to_integer(at(batch_reduced, a_vec.0[1])), to_integer(at(batch_reduced, a_vec.0[2])), to_integer(at(batch_reduced, a_vec.0[3])), to_integer(at(batch_reduced, b_vec.0[0])), to_integer(at(batch_reduced, b_vec.0[1])), to_integer(at(batch_reduced, b_vec.0[2])), to_integer(at(batch_reduced, b_vec.0[3]))), 65521) == adler_spec_b_u64(at(batch_reduced, bytes), ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(at(batch_reduced, a)), old(to_integer((self.b as u32)))) by solve();
      have to_integer(at(batch_reduced, a_vec.0[0])) <= 65520 by solve() using { to_integer(a_vec.0[0]) <= 65520; };
      have to_integer(at(batch_reduced, a_vec.0[1])) <= 65520 by solve() using { to_integer(a_vec.0[1]) <= 65520; };
      have to_integer(at(batch_reduced, a_vec.0[2])) <= 65520 by solve() using { to_integer(a_vec.0[2]) <= 65520; };
      have to_integer(at(batch_reduced, a_vec.0[3])) <= 65520 by solve() using { to_integer(a_vec.0[3]) <= 65520; };
      have to_integer(at(batch_reduced, b_vec.0[0])) <= 65520 by solve() using { to_integer(b_vec.0[0]) <= 65520; };
      have to_integer(at(batch_reduced, b_vec.0[1])) <= 65520 by solve() using { to_integer(b_vec.0[1]) <= 65520; };
      have to_integer(at(batch_reduced, b_vec.0[2])) <= 65520 by solve() using { to_integer(b_vec.0[2]) <= 65520; };
      have to_integer(at(batch_reduced, b_vec.0[3])) <= 65520 by solve() using { to_integer(b_vec.0[3]) <= 65520; };
      step_until(back_edge());
      have a_vec.0[0] == at(batch_reduced, a_vec.0[0]);
      have to_integer(a_vec.0[0]) <= 65520 by { rewrite(a_vec.0[0], at(batch_reduced, a_vec.0[0])); known(); }
      have a_vec.0[1] == at(batch_reduced, a_vec.0[1]);
      have to_integer(a_vec.0[1]) <= 65520 by { rewrite(a_vec.0[1], at(batch_reduced, a_vec.0[1])); known(); }
      have a_vec.0[2] == at(batch_reduced, a_vec.0[2]);
      have to_integer(a_vec.0[2]) <= 65520 by { rewrite(a_vec.0[2], at(batch_reduced, a_vec.0[2])); known(); }
      have a_vec.0[3] == at(batch_reduced, a_vec.0[3]);
      have to_integer(a_vec.0[3]) <= 65520 by { rewrite(a_vec.0[3], at(batch_reduced, a_vec.0[3])); known(); }
      have b_vec.0[0] == at(batch_reduced, b_vec.0[0]);
      have to_integer(b_vec.0[0]) <= 65520 by { rewrite(b_vec.0[0], at(batch_reduced, b_vec.0[0])); known(); }
      have b_vec.0[1] == at(batch_reduced, b_vec.0[1]);
      have to_integer(b_vec.0[1]) <= 65520 by { rewrite(b_vec.0[1], at(batch_reduced, b_vec.0[1])); known(); }
      have b_vec.0[2] == at(batch_reduced, b_vec.0[2]);
      have to_integer(b_vec.0[2]) <= 65520 by { rewrite(b_vec.0[2], at(batch_reduced, b_vec.0[2])); known(); }
      have b_vec.0[3] == at(batch_reduced, b_vec.0[3]);
      have to_integer(b_vec.0[3]) <= 65520 by { rewrite(b_vec.0[3], at(batch_reduced, b_vec.0[3])); known(); }
      have bytes == old(bytes) by known();
      have bytes.len() == old(bytes.len()) by known();
      have a <= 65520u32 by known();
      have b <= 65520u32 by known();
      have 22208u64 == 22208u64 by known();
      have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64 by known();
      have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64 by known();
      have remainder_len == bytes.len() % 4u64 by known();
      have to_integer(a_vec.0[0]) <= 65520 by known();
      have to_integer(a_vec.0[1]) <= 65520 by known();
      have to_integer(a_vec.0[2]) <= 65520 by known();
      have to_integer(a_vec.0[3]) <= 65520 by known();
      have to_integer(b_vec.0[0]) <= 65520 by known();
      have to_integer(b_vec.0[1]) <= 65520 by known();
      have to_integer(b_vec.0[2]) <= 65520 by known();
      have to_integer(b_vec.0[3]) <= 65520 by known();
      have (bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by known();
      have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) } by solve();
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a)) by {
       rewrite(a, at(batch_reduced, a));
       rewrite(a_vec.0[0], at(batch_reduced, a_vec.0[0]));
       rewrite(a_vec.0[1], at(batch_reduced, a_vec.0[1]));
       rewrite(a_vec.0[2], at(batch_reduced, a_vec.0[2]));
       rewrite(a_vec.0[3], at(batch_reduced, a_vec.0[3]));
       solve();
      }
      have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32)))) by solve();
      // The outer invariants at the back edge, one batch further on.
      have loop(0).iter.len() == at(outer_head, loop(0).iter.len()) - 1u64;
      have to_integer(loop(0).iter.len()) + (iterations + 1) == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) by solve() using { loop(0).iter.len() == at(outer_head, loop(0).iter.len()) - 1u64; 0u64 < at(outer_head, loop(0).iter.len()); to_integer(at(outer_head, loop(0).iter.len())) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64); };
      have iterations + 1 == (to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len())) by solve() using { to_integer(loop(0).iter.len()) + (iterations + 1) == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64); };
      have loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), iterations + 1) by { rewrite(iterations + 1, (to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64) - to_integer(loop(0).iter.len()))); known(); }
      have loop(0).iter.len() <= (bytes.len() - bytes.len() % 4u64) / 22208u64;
       // Every invariant at the back edge.
       have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len());
       have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
       have bytes == old(bytes);
       have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
       have bytes.len() == old(bytes.len());
       have a <= 65520u32;
       have b <= 65520u32;
       have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
       have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
       have to_integer(__rust_checked_93) == to_integer(bytes.len() - bytes.len() % 4u64);
       have __rust_checked_94 == 22208u64;
       have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
       have remainder_len == bytes.len() % 4u64;
       have to_integer(a_vec.0[0]) <= 65520;
       have to_integer(a_vec.0[1]) <= 65520;
       have to_integer(a_vec.0[2]) <= 65520;
       have to_integer(a_vec.0[3]) <= 65520;
       have to_integer(b_vec.0[0]) <= 65520;
       have to_integer(b_vec.0[1]) <= 65520;
       have to_integer(b_vec.0[2]) <= 65520;
       have to_integer(b_vec.0[3]) <= 65520;
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a));
       have 0 <= old(to_integer((self.b as u32)));
       have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32))));
       have loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), (iterations + 1));
       have to_integer(loop(0).iter.len()) + (iterations + 1) == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64);
       // The ranking members: the measure is read at the pass entry, before the header ran.
       have at(outer_head, loop(0).iter.len()) == at(outer_pass, loop(0).iter.len());
       have loop(0).iter.len() < at(outer_head, loop(0).iter.len()) by solve() using { loop(0).iter.len() == at(outer_head, loop(0).iter.len()) - 1u64; 0u64 < at(outer_head, loop(0).iter.len()); };
       have loop(0).iter.len() < at(outer_pass, loop(0).iter.len()) by solve() using { loop(0).iter.len() < at(outer_head, loop(0).iter.len()); at(outer_head, loop(0).iter.len()) == at(outer_pass, loop(0).iter.len()); };
      } else {
       // No chunk is left: the header test fails and the loop leaves by `break`.
       step();
       have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len());
       have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
       have bytes == old(bytes);
       have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
       have bytes.len() == old(bytes.len());
       have a <= 65520u32;
       have b <= 65520u32;
       have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
       have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
       have to_integer(__rust_checked_93) == to_integer(bytes.len() - bytes.len() % 4u64);
       have __rust_checked_94 == 22208u64;
       have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
       have remainder_len == bytes.len() % 4u64;
       have to_integer(a_vec.0[0]) <= 65520;
       have to_integer(a_vec.0[1]) <= 65520;
       have to_integer(a_vec.0[2]) <= 65520;
       have to_integer(a_vec.0[3]) <= 65520;
       have to_integer(b_vec.0[0]) <= 65520;
       have to_integer(b_vec.0[1]) <= 65520;
       have to_integer(b_vec.0[2]) <= 65520;
       have to_integer(b_vec.0[3]) <= 65520;
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a));
       have 0 <= old(to_integer((self.b as u32)));
       have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32))));
       have loop(0).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64), iterations);
       have to_integer(loop(0).iter.len()) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 22208u64);
       step();
      }
     }
     }
     have loop(0).iter.len() == 0u64;
     apply(adler_chunk_bytes_none(22208u64));
     have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == 0u64 by { rewrite(loop(0).iter.len(), 0u64); known(); }
     have adler_chunk_bytes(loop(0).iter.len(), 22208u64) < 22208u64 by solve() using { adler_chunk_bytes(loop(0).iter.len(), 22208u64) == 0u64; };
     apply(adler_outer_exhausted_remaining_u64(adler_chunk_bytes(loop(0).iter.len(), 22208u64))) using { adler_chunk_bytes(loop(0).iter.len(), 22208u64) < 22208u64; adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64; };
     have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) by { rewrite(adler_chunk_bytes(loop(0).iter.len(), 22208u64), 0u64); normalize(); }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64), to_integer(a)) by { rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)), to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); solve(); }
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)), to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); solve(); }
     apply(adler_outer_remainder_bounds_u64(bytes.len() - bytes.len() % 4u64)) using { (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; };
     apply(adler_outer_remainder_signed_bound_u64(bytes.len() - bytes.len() % 4u64)) using { (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; };
     apply(adler_outer_remainder_signed_divisible_u64(bytes.len() - bytes.len() % 4u64)) using { (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; };
     have remainder_chunk_len <= 22204u64 by { rewrite(remainder_chunk_len, (bytes.len() - bytes.len() % 4u64) % 22208u64); known(); }
     have remainder_chunk_len <= 2147483647u64 by normalize() using { remainder_chunk_len <= 22204u64; };
     have ((remainder_chunk_len as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(remainder_chunk_len, (bytes.len() - bytes.len() % 4u64) % 22208u64); normalize(); }
     have 0 <= ((remainder_chunk_len as u32) as i32) by { rewrite(((remainder_chunk_len as u32) as i32), ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); known(); }
     have remainder_chunk_len % 4u64 == 0u64 by { rewrite(remainder_chunk_len, (bytes.len() - bytes.len() % 4u64) % 22208u64); known(); }
     mark remainder_ctor;
     step_until(loop(2));
     // The remainder iterator covers the saved remainder in four-byte chunks.
     have loop(2).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64);
     have loop(2).iter.len() == remainder_chunk_len / 4u64 by {
      apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64));
      solve();
     }
     apply(adler_chunk_bytes_whole_4(remainder_chunk_len));
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) == remainder_chunk_len by { rewrite(loop(2).iter.len(), remainder_chunk_len / 4u64); known(); }
     have loop(2).iter.len() <= remainder_chunk_len / 4u64;
     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) == ((remainder_chunk_len as u32) as i32) by { rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), remainder_chunk_len); normalize(); }
     have ((remainder_chunk_len as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(remainder_chunk_len, (bytes.len() - bytes.len() % 4u64) % 22208u64); normalize(); }
     have 0 <= ((remainder_chunk_len as u32) as i32) by { rewrite(((remainder_chunk_len as u32) as i32), ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); known(); }
     have ((remainder_chunk_len as u32) as i32) <= 22204 by { rewrite(((remainder_chunk_len as u32) as i32), ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); known(); }
     have (((remainder_chunk_len as u32) as i32)) % 4 == 0 by { rewrite(((remainder_chunk_len as u32) as i32), ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); known(); }
     apply(adler_lane_initial_ceiling());
     apply(adler_lane_iterator_initial(((remainder_chunk_len as u32) as i32)));
     have adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == 0 by { rewrite(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32), ((remainder_chunk_len as u32) as i32)); known(); }
     have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); solve() using { to_integer(a_vec.0[0]) <= 65520; }; }
     have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); solve() using { to_integer(b_vec.0[0]) <= 65520; }; }
     have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); solve() using { to_integer(a_vec.0[1]) <= 65520; }; }
     have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); solve() using { to_integer(b_vec.0[1]) <= 65520; }; }
     have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); solve() using { to_integer(a_vec.0[2]) <= 65520; }; }
     have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); solve() using { to_integer(b_vec.0[2]) <= 65520; }; }
     have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); solve() using { to_integer(a_vec.0[3]) <= 65520; }; }
     have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); solve() using { to_integer(b_vec.0[3]) <= 65520; }; }
     have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) by { rewrite(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32), ((remainder_chunk_len as u32) as i32)); known(); }
     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32) by { rewrite(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32), ((remainder_chunk_len as u32) as i32)); normalize() using {}; }
     have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32) by known();
     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by { rewrite(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32), ((remainder_chunk_len as u32) as i32)); known(); }
     have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32));
     have bytes.len() == old(bytes.len()) by known();
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64 by solve() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) == remainder_chunk_len; remainder_chunk_len <= 22204u64; };
     apply(adler_bounded_count(remainder_chunk_len));
     have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk by { rewrite(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32), ((remainder_chunk_len as u32) as i32)); normalize(); }
     have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by {
      apply(adler_uint64_self_subtract(remainder_chunk_len)); rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), remainder_chunk_len); rewrite(to_integer(remainder_chunk_len - remainder_chunk_len), to_integer(0u64)); solve() using { (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk; };
     }
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk_len by { rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), remainder_chunk_len); normalize(); }
     have to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len()) by solve() using { bytes.len() % 4u64 <= bytes.len(); };
     have to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64)) by normalize();
     have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)) by solve() using { to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64)); bytes.len() % 4u64 <= bytes.len(); };
     have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer(bytes.len()) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)); to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len()); to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64)); bytes.len() % 4u64 <= bytes.len(); };
     have to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) by { rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), remainder_chunk_len); rewrite(remainder_chunk_len, (bytes.len() - bytes.len() % 4u64) % 22208u64); normalize(); }
     have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by { rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64))); solve() using { (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk; remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); }; }
     have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)) by { rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), remainder_chunk_len); rewrite(remainder_chunk_len, (bytes.len() - bytes.len() % 4u64) % 22208u64); known(); }
     have 0 <= to_integer(b);
     have to_integer(b) <= 4294967295;
     have 0 <= to_integer((b_vec.0[0]));
     have to_integer((b_vec.0[0])) <= 4294967295;
     have 0 <= to_integer((b_vec.0[1]));
     have to_integer((b_vec.0[1])) <= 4294967295;
     have 0 <= to_integer((b_vec.0[2]));
     have to_integer((b_vec.0[2])) <= 4294967295;
     have 0 <= to_integer((b_vec.0[3]));
     have to_integer((b_vec.0[3])) <= 4294967295;
     apply(adler_canonical_lane_b_floor(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]))) using { 0 <= to_integer(b); to_integer(a_vec.0[1]) <= 65520; to_integer(a_vec.0[2]) <= 65520; to_integer(a_vec.0[3]) <= 65520; 0 <= to_integer(b_vec.0[0]); 0 <= to_integer(b_vec.0[1]); 0 <= to_integer(b_vec.0[2]); 0 <= to_integer(b_vec.0[3]); };
     apply(adler_empty_remainder_position(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) using { 0 <= ((remainder_chunk_len as u32) as i32); ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) == ((remainder_chunk_len as u32) as i32); };
     have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))), 0); have to_integer(b) + 0 * to_integer(a) == to_integer(b) by solve() using {}; rewrite(to_integer(b) + 0 * to_integer(a), to_integer(b)); solve(); }
     // The remainder continues the uint64 running prefix at its cursor.
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a)) by { rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64))); solve(); }
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64))); rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))), 0); have to_integer(b) + 0 * to_integer(a) == to_integer(b) by solve() using {}; rewrite(to_integer(b) + 0 * to_integer(a), to_integer(b)); solve(); }
     have defined(((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32));
     loop {
      decreases loop(2).iter.len();
     invariant adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64;
      owns a_vec.0[0..4];
      owns b_vec.0[0..4];
      views *bytes;

      invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a));
      invariant 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
      invariant truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
      invariant adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk_len;
      invariant remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
      invariant (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64));
      invariant to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len() - bytes.len() % 4u64));
      invariant to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len());
      invariant bytes.len() % 4u64 <= bytes.len();
      invariant bytes == old(bytes);
      invariant bytes.len() == old(bytes.len());
      invariant a <= 65520u32;
      invariant b <= 65520u32;
      invariant 0 <= ((remainder_chunk_len as u32) as i32);
      invariant ((remainder_chunk_len as u32) as i32) <= 22204;
      invariant ((remainder_chunk_len as u32) as i32) % 4 == 0;
      invariant 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32);
      invariant ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
      invariant to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
      invariant remainder_len == bytes.len() % 4u64;
      invariant loop(2).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64), iterations);
      invariant to_integer(loop(2).iter.len()) + iterations == to_integer(remainder_chunk_len / 4u64);
      invariant remainder_chunk_len % 4u64 == 0u64;
      invariant remainder_chunk_len <= 22204u64;
      initialize by {
       have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64;
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a));
       have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
       have 0 <= old(to_integer((self.b as u32)));
       have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
       have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk_len;
       have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
       have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by { known(); known(); }
       have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len() - bytes.len() % 4u64));
       have to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len());
       have bytes.len() % 4u64 <= bytes.len();
       have bytes == old(bytes);
       have bytes.len() == old(bytes.len());
       have a <= 65520u32;
       have b <= 65520u32;
       have 0 <= ((remainder_chunk_len as u32) as i32);
       have ((remainder_chunk_len as u32) as i32) <= 22204;
       have ((remainder_chunk_len as u32) as i32) % 4 == 0;
       have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32);
       have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
       have remainder_len == bytes.len() % 4u64;
       have loop(2).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64), iterations) by {
        apply(chunks_exact::after_zero(chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64)));
        have loop(2).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64);
        solve();
       }
       have to_integer(loop(2).iter.len()) + iterations == to_integer(remainder_chunk_len / 4u64);
       have remainder_chunk_len % 4u64 == 0u64;
       have remainder_chunk_len <= 22204u64;
      }
      preserve by {
       mark remainder_pass;
       // The header reads `iter.len()` and leaves by `break` when it is zero.
       step(); step(); step(); step();
       if 0u64 < loop(2).iter.len() {
        have chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64).len() == remainder_chunk_len / 4u64 by {
         apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64));
        }
        have loop(2).iter.len() <= remainder_chunk_len / 4u64 by solve() using { to_integer(loop(2).iter.len()) + iterations == to_integer(remainder_chunk_len / 4u64); 0 <= iterations; };
        apply(integer::uint64_subtract_to_integer(remainder_chunk_len / 4u64, loop(2).iter.len()));
        have to_integer((remainder_chunk_len / 4u64 - loop(2).iter.len())) == iterations by solve() using { to_integer((remainder_chunk_len / 4u64 - loop(2).iter.len())) == to_integer(remainder_chunk_len / 4u64) - to_integer(loop(2).iter.len()); to_integer(loop(2).iter.len()) + iterations == to_integer(remainder_chunk_len / 4u64); };
        have (remainder_chunk_len / 4u64 - loop(2).iter.len()) < chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64).len() by solve() using { chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64).len() == remainder_chunk_len / 4u64; 0u64 < loop(2).iter.len(); loop(2).iter.len() <= remainder_chunk_len / 4u64; };
        have loop(2).iter.nth(0u64) == chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64).nth((remainder_chunk_len / 4u64 - loop(2).iter.len())) by {
         apply(chunks_exact::nth_after(chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64), iterations, 0u64, (remainder_chunk_len / 4u64 - loop(2).iter.len())));
         solve();
        }
        have loop(2).iter.nth(0u64).len() == 4u64 by {
         apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64, (remainder_chunk_len / 4u64 - loop(2).iter.len())));
         solve();
        }
        have loop(2).iter.after_next() == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64), iterations + 1) by {
         apply(chunks_exact::after_next_after(chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64), iterations));
         solve();
        }
        have loop(2).iter.after_next().len() == loop(2).iter.len() - 1u64 by {
         apply(chunks_exact::len_after_next(loop(2).iter));
        }
        apply(adler_chunk_bytes_next_4(loop(2).iter.len(), remainder_chunk_len));
        apply(adler_chunk_bytes_offset_whole_4(loop(2).iter.len(), remainder_chunk_len));
        have 4u64 <= adler_chunk_bytes(loop(2).iter.len(), 4u64);
        have to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) + 4u64) <= to_integer(remainder_chunk_len) by solve() using {
         adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk_len; 4u64 <= adler_chunk_bytes(loop(2).iter.len(), 4u64);
        };
        have 4 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) by {
         have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 2147483647u64 by solve() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64; };
         apply(adler_bounded_count_lower(adler_chunk_bytes(loop(2).iter.len(), 4u64), 4)); known();
        }
        have 4u64 <= adler_chunk_bytes(loop(2).iter.len(), 4u64);
        have to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len() - bytes.len() % 4u64)) by solve() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer(bytes.len()) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len() - bytes.len() % 4u64)); to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len()); to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(4u64) <= to_integer(bytes.len() - ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by solve() using { 4u64 <= adler_chunk_bytes(loop(2).iter.len(), 4u64); to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)); to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len()); bytes.len() % 4u64 <= bytes.len(); };
        // The first fact about the chunk's pointer is its offset from `bytes`: the helper call
        // below reads the chunk through the input's view, and the view is found by that fact.
        have loop(2).iter.nth(0u64).as_ptr() == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by {
         have loop(2).iter.nth(0u64).as_ptr() == remainder_chunk + (remainder_chunk_len / 4u64 - loop(2).iter.len()) * 4u64 by {
          apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64, (remainder_chunk_len / 4u64 - loop(2).iter.len())));
          solve();
         }
         have loop(2).iter.nth(0u64).as_ptr() == remainder_chunk + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by {
          rewrite(to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer((remainder_chunk_len / 4u64 - loop(2).iter.len()) * 4u64));
          known();
         }
         apply(integer::uint64_subtract_to_integer(remainder_chunk_len, adler_chunk_bytes(loop(2).iter.len(), 4u64)));
         apply(integer::uint64_subtract_to_integer((bytes.len() - bytes.len() % 4u64), adler_chunk_bytes(loop(2).iter.len(), 4u64)));
         have to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64)) by normalize();
         apply(integer::uint64_subtract_to_integer((bytes.len() - bytes.len() % 4u64), (bytes.len() - bytes.len() % 4u64) % 22208u64));
         have to_integer(remainder_chunk_len) == to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) by solve() using { remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64; };
         have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by solve() using { to_integer(remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(remainder_chunk_len) - to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer((bytes.len() - bytes.len() % 4u64)) - to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) == to_integer((bytes.len() - bytes.len() % 4u64)) - to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64); to_integer(remainder_chunk_len) == to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64); };
         have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= 18446744073709551615 by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer(bytes.len()); };
         apply(integer::uint64_add_to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64), (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))));
         have remainder_chunk + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by { rewrite(remainder_chunk, bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= 18446744073709551615; to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))); }; }
         have to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
         rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))));
         solve() using { loop(2).iter.nth(0u64).as_ptr() == remainder_chunk + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)); remainder_chunk + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
        }
        apply(integer::uint64_subtract_to_integer(remainder_chunk_len, adler_chunk_bytes(loop(2).iter.len(), 4u64)));
        apply(integer::uint64_subtract_to_integer((bytes.len() - bytes.len() % 4u64), adler_chunk_bytes(loop(2).iter.len(), 4u64)));
        have to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) <= to_integer((bytes.len() - bytes.len() % 4u64)) by normalize();
        apply(integer::uint64_subtract_to_integer((bytes.len() - bytes.len() % 4u64), (bytes.len() - bytes.len() % 4u64) % 22208u64));
        have to_integer(remainder_chunk_len) == to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64) by solve() using { remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64; };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by solve() using { to_integer(remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(remainder_chunk_len) - to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer((bytes.len() - bytes.len() % 4u64)) - to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) == to_integer((bytes.len() - bytes.len() % 4u64)) - to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64); to_integer(remainder_chunk_len) == to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64); };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= 18446744073709551615 by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer(bytes.len()); };
        apply(integer::uint64_add_to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64), (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))));
        have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
        apply(integer::uint64_subtract_to_integer(bytes.len(), ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))));
        have to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()) by solve() using { to_integer(4u64) <= to_integer(bytes.len() - ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(bytes.len() - ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(bytes.len()) - to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) < to_integer(bytes.len()) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(3u64) <= 18446744073709551615 by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        apply(integer::uint64_add_to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64)), 3u64));
        have to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) + 3u64) < to_integer(bytes.len()) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) + 3u64) == to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(3u64); to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) < to_integer(bytes.len()) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) < to_integer(bytes.len()); };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 3 < to_integer(bytes.len()) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) + to_integer((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        // The same chunk starts `remainder_chunk_len - remaining` bytes into the remainder, where the old cursor stood.
        have loop(2).iter.nth(0u64).as_ptr() == remainder_chunk + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by {
         have loop(2).iter.nth(0u64).as_ptr() == remainder_chunk + (remainder_chunk_len / 4u64 - loop(2).iter.len()) * 4u64 by {
          apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64, (remainder_chunk_len / 4u64 - loop(2).iter.len())));
          solve();
         }
         rewrite(to_integer(remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)), to_integer((remainder_chunk_len / 4u64 - loop(2).iter.len()) * 4u64));
         known();
        }
        have remainder_chunk_len <= 22208u64 by solve() using { remainder_chunk_len <= 22204u64; };
        have remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64 by solve() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk_len; remainder_chunk_len <= 22208u64; };
        apply(adler_count_byte_pointer(remainder_chunk, remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)));
        apply(adler_count_step(remainder_chunk_len, adler_chunk_bytes(loop(2).iter.len(), 4u64)));
        have loop(2).iter.nth(0u64).as_ptr() == (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by {
         rewrite(to_integer(((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), to_integer((((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) as uint32) as int32)));
         solve() using { loop(2).iter.nth(0u64).as_ptr() == remainder_chunk + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)); remainder_chunk + (remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == remainder_chunk + (((remainder_chunk_len - adler_chunk_bytes(loop(2).iter.len(), 4u64)) as uint32) as int32); };
        }
        mark lane_head;
        have at(lane_head, loop(2).iter.nth(0u64).as_ptr()) == at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have at(lane_head, loop(2).iter.nth(0u64).len()) == 4u64;
        have 0u64 < at(lane_head, loop(2).iter.len());
        have to_integer(adler_chunk_bytes(at(lane_head, loop(2).iter.len()) - 1u64, 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64);
        have at(lane_head, loop(2).iter.after_next()) == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64), iterations + 1);
        have to_integer(at(lane_head, loop(2).iter.len())) + iterations == to_integer(remainder_chunk_len / 4u64);
        have at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) % 4 == 0;
        have at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32);
        have 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32));
        have 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32));
        have ((remainder_chunk_len as u32) as i32) <= 22208 by solve() using { ((remainder_chunk_len as u32) as i32) <= 22204; };

        have 0 <= to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { 0 <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); };
        have to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) + 4) <= to_integer(((remainder_chunk_len as u32) as i32)) by solve() using { 0 <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); };
        have to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) <= 22204 by solve() using { 0 <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); };
        step_until(assignment(__rust_mir_69, 0)); step();
        have __rust_mir_69 == at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        step_until(assignment(__rust_mir_69_len, 0)); step();
        have __rust_mir_69_len == 4u64;
        have loop(2).iter == at(lane_head, loop(2).iter.after_next());
        have loop(2).iter.len() == at(lane_head, loop(2).iter.len()) - 1u64;
        have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64) by { rewrite(loop(2).iter.len(), at(lane_head, loop(2).iter.len()) - 1u64); known(); }
        have 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64));
        have at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= 22208u64;
        apply(integer::uint64_subtract_to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)), 4u64));
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) == at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64 by solve() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) - to_integer(4u64); };
        apply(adler_count_lane_step(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))));
        have to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4);
        have to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
        have 0 <= to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) by { rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))))); known(); }
        have to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) <= 22204 by { rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))))); known(); }
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); };
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
        have __rust_mir_69 == remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) by {
         rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))));
         solve() using { __rust_mir_69 == at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) == remainder_chunk + (((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); };
        }
        apply(adler_current_window(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) using { 0 <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32); ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32); };



        mark byte_view;
        step_until(assignment(__rust_mir_68, 0));
        have __rust_checked_22 == __rust_mir_69;
        have __rust_checked_22 == at(byte_view, __rust_mir_69);
        have __rust_mir_69 == at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) by known();
        have __rust_checked_22 == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) by solve() using { __rust_checked_22 == __rust_mir_69; __rust_mir_69 == at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
        have __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) by solve() using { __rust_checked_22 == __rust_mir_69; __rust_checked_22 == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))); };

        have to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer((bytes.len() - bytes.len() % 4u64)) by solve() using { to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len() - bytes.len() % 4u64)); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer(bytes.len()) by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer((bytes.len() - bytes.len() % 4u64)); to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len()); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len() - bytes.len() % 4u64)); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(4u64) <= to_integer(bytes.len() - ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) by solve() using { 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len() - bytes.len() % 4u64)); to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len()); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64) by solve() using { 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len() - bytes.len() % 4u64)); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) + 4 <= 18446744073709551615 by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64); };
        mark remainder_constructor;
        step();
        step_until(assignment(__rust_mir_71, 0));
        mark vector_a;
        // Use the checked constructor's exact call-entry byte observations.
        have at(remainder_constructor, __rust_checked_22) == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) by solve() using { __rust_checked_22 == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
        have to_integer(at(vector_a, __rust_mir_68.0[0])) == at(remainder_constructor, to_integer((__rust_checked_22[0] as i32))) by normalize() using { to_integer(__rust_mir_68.0[0]) == at(remainder_constructor, to_integer((__rust_checked_22[0] as i32))); };
        have at(remainder_constructor, (__rust_checked_22[0] as i32)) == at(remainder_constructor, ((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32)) by {
         rewrite(at(remainder_constructor, __rust_checked_22), bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))); solve();
        }
        have to_integer(at(vector_a, __rust_mir_68.0[0])) == at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_68.0[0])), at(remainder_constructor, to_integer((__rust_checked_22[0] as i32))));
         rewrite(at(remainder_constructor, (__rust_checked_22[0] as i32)), at(remainder_constructor, ((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32)));
         normalize();
        }
        have at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32))) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32))) by solve();
        have to_integer(at(vector_a, __rust_mir_68.0[0])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_68.0[0])), at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32)))); known();
        }
        have to_integer(at(vector_a, __rust_mir_68.0[1])) == at(remainder_constructor, to_integer((__rust_checked_22[1] as i32))) by normalize() using { to_integer(__rust_mir_68.0[1]) == at(remainder_constructor, to_integer((__rust_checked_22[1] as i32))); };
        have at(remainder_constructor, (__rust_checked_22[1] as i32)) == at(remainder_constructor, ((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32)) by {
         rewrite(at(remainder_constructor, __rust_checked_22), bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))); solve();
        }
        have to_integer(at(vector_a, __rust_mir_68.0[1])) == at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_68.0[1])), at(remainder_constructor, to_integer((__rust_checked_22[1] as i32))));
         rewrite(at(remainder_constructor, (__rust_checked_22[1] as i32)), at(remainder_constructor, ((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32)));
         normalize();
        }
        have at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32))) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32))) by solve();
        have to_integer(at(vector_a, __rust_mir_68.0[1])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_68.0[1])), at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32)))); known();
        }
        have to_integer(at(vector_a, __rust_mir_68.0[2])) == at(remainder_constructor, to_integer((__rust_checked_22[2] as i32))) by normalize() using { to_integer(__rust_mir_68.0[2]) == at(remainder_constructor, to_integer((__rust_checked_22[2] as i32))); };
        have at(remainder_constructor, (__rust_checked_22[2] as i32)) == at(remainder_constructor, ((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32)) by {
         rewrite(at(remainder_constructor, __rust_checked_22), bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))); solve();
        }
        have to_integer(at(vector_a, __rust_mir_68.0[2])) == at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_68.0[2])), at(remainder_constructor, to_integer((__rust_checked_22[2] as i32))));
         rewrite(at(remainder_constructor, (__rust_checked_22[2] as i32)), at(remainder_constructor, ((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32)));
         normalize();
        }
        have at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32))) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32))) by solve();
        have to_integer(at(vector_a, __rust_mir_68.0[2])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_68.0[2])), at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32)))); known();
        }
        have to_integer(at(vector_a, __rust_mir_68.0[3])) == at(remainder_constructor, to_integer((__rust_checked_22[3] as i32))) by normalize() using { to_integer(__rust_mir_68.0[3]) == at(remainder_constructor, to_integer((__rust_checked_22[3] as i32))); };
        have at(remainder_constructor, (__rust_checked_22[3] as i32)) == at(remainder_constructor, ((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32)) by {
         rewrite(at(remainder_constructor, __rust_checked_22), bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))); solve();
        }
        have to_integer(at(vector_a, __rust_mir_68.0[3])) == at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_68.0[3])), at(remainder_constructor, to_integer((__rust_checked_22[3] as i32))));
         rewrite(at(remainder_constructor, (__rust_checked_22[3] as i32)), at(remainder_constructor, ((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32)));
         normalize();
        }
        have at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32))) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32))) by solve();
        have to_integer(at(vector_a, __rust_mir_68.0[3])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32))) by {
         rewrite(to_integer(at(vector_a, __rust_mir_68.0[3])), at(remainder_constructor, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32)))); known();
        }
        have 0 <= to_integer(at(vector_a, a_vec.0[0]));
        have 0 <= to_integer(at(vector_a, b_vec.0[0]));
        have to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, __rust_mir_68.0[0]));
        have to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255;
        apply(adler_lane_iterator_add_contracts(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_68.0[0]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[0])); to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[0])); to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255; };
        apply(adler_lane_iterator_native_preservation(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_68.0[0]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[0])); to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[0])); to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255; };
        have 0 <= to_integer(at(vector_a, a_vec.0[1]));
        have 0 <= to_integer(at(vector_a, b_vec.0[1]));
        have to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, __rust_mir_68.0[1]));
        have to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255;
        apply(adler_lane_iterator_add_contracts(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_68.0[1]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[1])); to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[1])); to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255; };
        apply(adler_lane_iterator_native_preservation(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_68.0[1]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[1])); to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[1])); to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255; };
        have 0 <= to_integer(at(vector_a, a_vec.0[2]));
        have 0 <= to_integer(at(vector_a, b_vec.0[2]));
        have to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, __rust_mir_68.0[2]));
        have to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255;
        apply(adler_lane_iterator_add_contracts(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_68.0[2]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[2])); to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[2])); to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255; };
        apply(adler_lane_iterator_native_preservation(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_68.0[2]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[2])); to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[2])); to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255; };
        have 0 <= to_integer(at(vector_a, a_vec.0[3]));
        have 0 <= to_integer(at(vector_a, b_vec.0[3]));
        have to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, __rust_mir_68.0[3]));
        have to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255;
        apply(adler_lane_iterator_add_contracts(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[3]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[3])); to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[3])); to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255; };
        apply(adler_lane_iterator_native_preservation(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[3]))) using { 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[3])); to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, b_vec.0[3])); to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255; };
        have to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(vector_a, bytes), ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(a)) by { solve(); }
        have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) by { have to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); }; rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); solve(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[0]), at(vector_a, __rust_mir_68.0[0]))) using { to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) <= 4294967295; };
        have to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])), to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))); known(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[1]), at(vector_a, __rust_mir_68.0[1]))) using { to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) <= 4294967295; };
        have to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))); known(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[2]), at(vector_a, __rust_mir_68.0[2]))) using { to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) <= 4294967295; };
        have to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))); known(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[3]), at(vector_a, __rust_mir_68.0[3]))) using { to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) <= 4294967295; };
        have to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))); known(); }
        apply(adler_native_deferred_b_step((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[0]), at(vector_a, __rust_mir_68.0[1]), at(vector_a, __rust_mir_68.0[2]), at(vector_a, __rust_mir_68.0[3]))) using { 0 <= to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)); to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) <= 22204; 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) <= 4294967295; to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3]))) <= 4294967295; };
        apply(adler_nonnegative_deferred_b_step((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[0]), at(vector_a, __rust_mir_68.0[1]), at(vector_a, __rust_mir_68.0[2]), at(vector_a, __rust_mir_68.0[3]))) using { 0 <= to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)); to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) <= 22204; 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) <= 4294967295; to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3]))) <= 4294967295; };
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b_u64(at(vector_a, bytes), ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(at(vector_a, a)), old(to_integer((self.b as u32)))) by { have to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); }; rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); solve(); }
        apply(adler_native_deferred_b_prefix_step_u64(at(vector_a, bytes), ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4), to_integer(a), old(to_integer((self.b as u32))), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[0]), at(vector_a, __rust_mir_68.0[1]), at(vector_a, __rust_mir_68.0[2]), at(vector_a, __rust_mir_68.0[3]))) using {
         to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) + 4 <= 18446744073709551615;
         0 <= to_integer(a); to_integer(a) <= 65520;
         truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(vector_a, bytes), ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(a));
         to_integer(at(vector_a, __rust_mir_68.0[0])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32)));
         to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_68.0[1])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32)));
         to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_68.0[2])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32)));
         to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_68.0[3])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32)));
         to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) <= 4294967295;
         0 <= to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)); to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) <= 22204; 0 <= old(to_integer((self.b as u32))); 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b_u64(at(vector_a, bytes), ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(at(vector_a, a)), old(to_integer((self.b as u32)))); to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3]))) <= 4294967295;
        };
        apply(adler_native_four_lane_a_prefix_step_u64(at(vector_a, bytes), ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(a), to_integer(a), at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, __rust_mir_68.0[0]), at(vector_a, __rust_mir_68.0[1]), at(vector_a, __rust_mir_68.0[2]), at(vector_a, __rust_mir_68.0[3]))) using {
         to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) + 4 <= 18446744073709551615;
         0 <= to_integer(a); to_integer(a) <= 65520;
         truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(vector_a, bytes), ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(a));
         to_integer(at(vector_a, __rust_mir_68.0[0])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32)));
         to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_68.0[1])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32)));
         to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_68.0[2])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32)));
         to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) <= 4294967295;
         to_integer(at(vector_a, __rust_mir_68.0[3])) == at(vector_a, to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32)));
         to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) <= 4294967295;
        };
        step_until(assignment(__rust_mir_74, 0));
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]));
        have b_vec.0[0] == at(vector_a, b_vec.0[0]);
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])) by solve() using { b_vec.0[0] == at(vector_a, b_vec.0[0]); };
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) by solve() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); };
        have to_integer(b_vec.0[0]) + to_integer(a_vec.0[0]) <= 4294967295 by solve() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])); to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) <= 4294967295; };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]));
        have b_vec.0[1] == at(vector_a, b_vec.0[1]);
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])) by solve() using { b_vec.0[1] == at(vector_a, b_vec.0[1]); };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); };
        have to_integer(b_vec.0[1]) + to_integer(a_vec.0[1]) <= 4294967295 by solve() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) <= 4294967295; };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]));
        have b_vec.0[2] == at(vector_a, b_vec.0[2]);
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])) by solve() using { b_vec.0[2] == at(vector_a, b_vec.0[2]); };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); };
        have to_integer(b_vec.0[2]) + to_integer(a_vec.0[2]) <= 4294967295 by solve() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) <= 4294967295; };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]));
        have b_vec.0[3] == at(vector_a, b_vec.0[3]);
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])) by solve() using { b_vec.0[3] == at(vector_a, b_vec.0[3]); };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); };
        have to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]) <= 4294967295 by solve() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) <= 4294967295; };
        mark vector_b;
        step_until(back_edge());
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]));
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])));
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) by solve() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) by solve() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]));
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])));
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) by solve() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]));
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])));
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) by solve() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]));
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])));
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) by solve() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); };
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32) by known();
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by { rewrite(to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); normalize() using { at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) % 4 == 0; 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; }; }
        have to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) + 4) == to_integer(((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
        have 0 <= to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by solve() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
        have to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) <= 22200 by solve() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
        have to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) <= 22204 by solve() using { to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) <= 22200; };
        have 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) by solve() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); };
        have defined(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));


        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) < at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
        have bytes == old(bytes) by known();
        have bytes.len() == old(bytes.len()) by known();
        have a <= 65520u32 by known();
        have b <= 65520u32 by known();
        have 0 <= ((remainder_chunk_len as u32) as i32) by known();
        have ((remainder_chunk_len as u32) as i32) <= 22204 by known();
        have ((remainder_chunk_len as u32) as i32) % 4 == 0 by known();
        have 4u64 == 4u64 by known();
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32) by known();
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by known();

        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by known();
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by known();

        have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64 by known();
        have remainder_len == bytes.len() % 4u64 by known();
        have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64);
        have 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) by known();
        have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len() - bytes.len() % 4u64)) by solve() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len() - bytes.len() % 4u64)); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64) by solve() using { 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len() - bytes.len() % 4u64)); bytes.len() % 4u64 <= bytes.len(); };
        // The cursor term advanced by four bytes with the count.
        apply(adler_bounded_pointer_association(remainder_chunk, (((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))))) using { 0 <= to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) <= 22204; };
        have at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) == remainder_chunk + (((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) + 4 by { rewrite(at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))), remainder_chunk + (((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); rewrite((remainder_chunk + (((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) + 4, remainder_chunk + ((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) + 4)); rewrite(to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) + 4), to_integer(((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); normalize() using {}; }
        have to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615 by solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64); };
        apply(integer::uint64_add_to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), 4u64));
        have __rust_mir_69 + 4 == bytes + (((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64) by { rewrite(__rust_mir_69, bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))); solve() using { to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615; to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64) == to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) + to_integer(4u64); }; }
        have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == __rust_mir_69 + 4 by { rewrite(__rust_mir_69, at(lane_head, (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))))); known(); }
        have to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64) by solve() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len() - bytes.len() % 4u64)); bytes.len() % 4u64 <= bytes.len(); };
        have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by { rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64)); solve() using { (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == __rust_mir_69 + 4; __rust_mir_69 + 4 == bytes + (((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64); }; }
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64 by solve() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= 22208u64; };
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk_len by solve() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= remainder_chunk_len; };
        apply(adler_bounded_pointer_association(remainder_chunk, (((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))))) using { 0 <= to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) <= 22204; };
        have to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk_len as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) + 4) by solve() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
        have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32));
        // A advances at the uint64 cursor, using the real iterator state.
        have to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4) == to_integer(((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) by solve() using { 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32); ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 0 <= to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)); };
        have defined((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by known();
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a)) by {
         rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64));
         rewrite(to_integer(a_vec.0[0]), to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])));
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])));
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])));
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])));
         solve();
        }
        have to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by { rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4), to_integer(((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); normalize(); }
        have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by {
         have to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by solve() using { to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4); };
         rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))), to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4));
         have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); };
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])));
         have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); };
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])));
         have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); };
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])));
         have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) by solve() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))); };
         rewrite(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))));
         have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) by solve() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))); };
         rewrite(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))));
         have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) by solve() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))); };
         rewrite(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))));
         have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) by solve() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))); };
         rewrite(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))));
         solve();
        }
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32)))) by {
         rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64));
         have to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by solve() using { to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4); };
         rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))), to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4));
         have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); };
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])));
         have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); };
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])));
         have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); };
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])));
         have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) by solve() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))); };
         rewrite(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))));
         have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) by solve() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))); };
         rewrite(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))));
         have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) by solve() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))); };
         rewrite(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))));
         have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) by solve() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))); };
         rewrite(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))));
         solve();
        }
        // The invariants at the back edge, one pass further on.
        have loop(2).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64), iterations + 1);
        have to_integer(loop(2).iter.len()) + (iterations + 1) == to_integer(remainder_chunk_len / 4u64) by solve() using { loop(2).iter.len() == at(lane_head, loop(2).iter.len()) - 1u64; 0u64 < at(lane_head, loop(2).iter.len()); to_integer(at(lane_head, loop(2).iter.len())) + iterations == to_integer(remainder_chunk_len / 4u64); };
        have loop(2).iter.len() <= remainder_chunk_len / 4u64 by solve() using { to_integer(loop(2).iter.len()) + (iterations + 1) == to_integer(remainder_chunk_len / 4u64); 0 <= iterations; };
        have remainder_chunk_len % 4u64 == 0u64;
        have remainder_chunk_len <= 22204u64;
        // Every invariant at the back edge.
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64;
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a));
        have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
        have 0 <= old(to_integer((self.b as u32)));
        have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk_len;
        have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
        have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64));
        have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len() - bytes.len() % 4u64));
        have to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len());
        have bytes.len() % 4u64 <= bytes.len();
        have bytes == old(bytes);
        have bytes.len() == old(bytes.len());
        have a <= 65520u32;
        have b <= 65520u32;
        have 0 <= ((remainder_chunk_len as u32) as i32);
        have ((remainder_chunk_len as u32) as i32) <= 22204;
        have ((remainder_chunk_len as u32) as i32) % 4 == 0;
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32);
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
        have remainder_len == bytes.len() % 4u64;
        have loop(2).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64), (iterations + 1));
        have to_integer(loop(2).iter.len()) + (iterations + 1) == to_integer(remainder_chunk_len / 4u64);
        have remainder_chunk_len % 4u64 == 0u64;
        have remainder_chunk_len <= 22204u64;
        // The ranking members: the measure is read at the pass entry, before the header ran.
        have at(lane_head, loop(2).iter.len()) == at(remainder_pass, loop(2).iter.len());
        have loop(2).iter.len() < at(lane_head, loop(2).iter.len()) by solve() using { loop(2).iter.len() == at(lane_head, loop(2).iter.len()) - 1u64; 0u64 < at(lane_head, loop(2).iter.len()); };
        have loop(2).iter.len() < at(remainder_pass, loop(2).iter.len()) by solve() using { loop(2).iter.len() < at(lane_head, loop(2).iter.len()); at(lane_head, loop(2).iter.len()) == at(remainder_pass, loop(2).iter.len()); };
       } else {
        // No chunk is left: the header test fails and the loop leaves by `break`.
        step();
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64;
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a));
        have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
        have 0 <= old(to_integer((self.b as u32)));
        have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk_len;
        have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
        have (remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64));
        have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len() - bytes.len() % 4u64));
        have to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(bytes.len());
        have bytes.len() % 4u64 <= bytes.len();
        have bytes == old(bytes);
        have bytes.len() == old(bytes.len());
        have a <= 65520u32;
        have b <= 65520u32;
        have 0 <= ((remainder_chunk_len as u32) as i32);
        have ((remainder_chunk_len as u32) as i32) <= 22204;
        have ((remainder_chunk_len as u32) as i32) % 4 == 0;
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk_len as u32) as i32);
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
        have remainder_len == bytes.len() % 4u64;
        have loop(2).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(remainder_chunk, remainder_chunk_len), 4u64), iterations);
        have to_integer(loop(2).iter.len()) + iterations == to_integer(remainder_chunk_len / 4u64);
        have remainder_chunk_len % 4u64 == 0u64;
        have remainder_chunk_len <= 22204u64;
        step();
       }
      }
     }
     have loop(2).iter.len() == 0u64;
     apply(adler_chunk_bytes_none(4u64));
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) == 0u64 by { rewrite(loop(2).iter.len(), 0u64); known(); }
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) < 4u64 by solve() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) == 0u64; };
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 3u64 by solve() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) < 4u64; };
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 2147483647u64 by solve() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 3u64; };
     apply(adler_bounded_count_upper(adler_chunk_bytes(loop(2).iter.len(), 4u64), 3));
     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) < 4 by solve() using { ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= 3; };

     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) by normalize() using { 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32); ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) < 4; };
     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) == 0 by solve() using { ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0; ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32); };
     apply(adler_bounded_count(adler_chunk_bytes(loop(2).iter.len(), 4u64)));
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) == 0u64 by solve() using { (((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) as uint64) == adler_chunk_bytes(loop(2).iter.len(), 4u64); ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) == 0; };

     have to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer((bytes.len() - bytes.len() % 4u64)) by { rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), 0u64); normalize(); }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(a)) by { rewrite(to_integer((bytes.len() - bytes.len() % 4u64)), to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); solve(); }
     apply(adler_complete_remainder_position(((remainder_chunk_len as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) using { 0 <= ((remainder_chunk_len as u32) as i32); ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) == 0; };
     have 0 <= adler_lane_b(to_integer(b) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(to_integer(((remainder_chunk_len as u32) as i32)), to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); known(); }
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(to_integer(((remainder_chunk_len as u32) as i32)), to_integer((((remainder_chunk_len as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); rewrite(to_integer((bytes.len() - bytes.len() % 4u64)), to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); solve(); }
     mark remainder_lane_prefix;

     have truncating_remainder(adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32))));
     have 0 <= adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3])));
     have truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(at(remainder_lane_prefix, a)));
     have 0 <= to_integer((at(remainder_lane_prefix, a)));
     have to_integer((at(remainder_lane_prefix, a))) <= 4294967295;
     have 0 <= to_integer((at(remainder_lane_prefix, a_vec.0[0])));
     have to_integer((at(remainder_lane_prefix, a_vec.0[0]))) <= 4294967295;
     have 0 <= to_integer((at(remainder_lane_prefix, a_vec.0[1])));
     have to_integer((at(remainder_lane_prefix, a_vec.0[1]))) <= 4294967295;
     have 0 <= to_integer((at(remainder_lane_prefix, a_vec.0[2])));
     have to_integer((at(remainder_lane_prefix, a_vec.0[2]))) <= 4294967295;
     have 0 <= to_integer((at(remainder_lane_prefix, a_vec.0[3])));
     have to_integer((at(remainder_lane_prefix, a_vec.0[3]))) <= 4294967295;
     apply(adler_lane_a_reduction(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])))) using { 0 <= to_integer(at(remainder_lane_prefix, a)); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[0])); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[1])); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[2])); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[3])); };
     have remainder_len == bytes.len() % 4u64 by known();
     step_until(assignment(__rust_mir_80, 0)); step();
     have __rust_mir_77 == (remainder_chunk_len as u32);
     have remainder_chunk_len <= 22204u64 by { rewrite(remainder_chunk_len, (bytes.len() - bytes.len() % 4u64) % 22208u64); known(); }
     apply(adler_small_length_cast(remainder_chunk_len)) using { remainder_chunk_len <= 22204u64; };
     have __rust_mir_77 <= 22204u32 by { rewrite(__rust_mir_77, (remainder_chunk_len as u32)); known(); }
     have __rust_mir_80 <= 65520u32 by solve() using { a <= 65520u32; };
     apply(adler_scalar_batch_product_bound(__rust_mir_77, __rust_mir_80)) using { __rust_mir_77 <= 22204u32; __rust_mir_80 <= 65520u32; };
     have to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 4294967295 by solve() using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 1454806080; };
     apply(integer::uint32_multiply_guard_by_integer_bound(__rust_mir_77, __rust_mir_80)) using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 4294967295; };
     have remainder_chunk_len <= 22208u64 by solve() using { remainder_chunk_len <= 22204u64; };
     apply(adler_count_observation(remainder_chunk_len)) using { remainder_chunk_len <= 22208u64; };
     apply(adler_remainder_native_count_observation(remainder_chunk_len)) using { remainder_chunk_len <= 22204u64; };
     have to_integer(__rust_mir_77) == to_integer(((remainder_chunk_len as u32) as i32)) by { rewrite(__rust_mir_77, (remainder_chunk_len as u32)); solve() using { to_integer((remainder_chunk_len as u32)) == to_integer(remainder_chunk_len); to_integer(((remainder_chunk_len as u32) as i32)) == to_integer(remainder_chunk_len); }; }
     mark seed_product;
     have to_integer(at(seed_product, __rust_mir_77)) == to_integer(((remainder_chunk_len as u32) as i32));
     have to_integer(at(seed_product, __rust_mir_80)) == to_integer(at(remainder_lane_prefix, a));
     have to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80)) <= 1454806080 by solve() using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 1454806080; };
     have at(seed_product, __rust_mir_80) == 0u32 or at(seed_product, __rust_mir_77) <= 4294967295u32 / at(seed_product, __rust_mir_80) by solve() using { __rust_mir_80 == 0u32 or __rust_mir_77 <= 4294967295u32 / __rust_mir_80; };
     apply(integer::uint32_multiply_to_integer(at(seed_product, __rust_mir_77), at(seed_product, __rust_mir_80))) using { at(seed_product, __rust_mir_80) == 0u32 or at(seed_product, __rust_mir_77) <= 4294967295u32 / at(seed_product, __rust_mir_80); };
     if __rust_mir_80 == 0u32 {
      step_until(assignment(__rust_mir_76, 0)); step();
     } else {
      have __rust_mir_77 <= 4294967295u32 / __rust_mir_80 by {
       cases {
        __rust_mir_80 == 0u32 => { contradiction(not (__rust_mir_80 == 0u32)); }
        __rust_mir_77 <= 4294967295u32 / __rust_mir_80 => { known(); }
       }
      }
      step_until(assignment(__rust_mir_76, 0)); step();
     }
     have to_integer(__rust_mir_76) == to_integer(at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80));
     have to_integer(__rust_mir_76) == to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)) by { rewrite(to_integer(__rust_mir_76), to_integer(at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80))); rewrite(to_integer(at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)), to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80))); rewrite(to_integer(at(seed_product, __rust_mir_77)), to_integer(((remainder_chunk_len as u32) as i32))); rewrite(to_integer(at(seed_product, __rust_mir_80)), to_integer(at(remainder_lane_prefix, a))); solve(); }
     have to_integer(__rust_mir_76) <= 1454806080 by { rewrite(to_integer(__rust_mir_76), to_integer(at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80))); rewrite(to_integer(at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)), to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80))); known(); }
     have b <= 65520u32 by known();
     have to_integer(b) + to_integer(__rust_mir_76) <= 4294967295 by solve() using { to_integer(b) <= 65520; to_integer(__rust_mir_76) <= 1454806080; };
     have b <= 4294967295u32 - __rust_mir_76 by solve() using { to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; };
     mark deferred_b;
     have to_integer(at(deferred_b, b)) == to_integer(at(remainder_lane_prefix, b));
     have to_integer(at(deferred_b, __rust_mir_76)) == to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a));
     have to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)) <= 4294967295 by solve() using { to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; };
     have to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)) == to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)) by apply(integer::uint32_add_to_integer(at(deferred_b, b), at(deferred_b, __rust_mir_76))) using { to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)) <= 4294967295; };
     step_until(assignment(__rust_mir_84, 0)); step();
     mark reduction_a;
     have to_integer(at(reduction_a, a_vec.0[0])) == to_integer(at(remainder_lane_prefix, a_vec.0[0]));
     have to_integer(at(reduction_a, a_vec.0[1])) == to_integer(at(remainder_lane_prefix, a_vec.0[1]));
     have to_integer(at(reduction_a, a_vec.0[2])) == to_integer(at(remainder_lane_prefix, a_vec.0[2]));
     have to_integer(at(reduction_a, a_vec.0[3])) == to_integer(at(remainder_lane_prefix, a_vec.0[3]));
     step_until(assignment(__rust_mir_86, 0)); step();
     mark reduction_b;
     have to_integer(at(reduction_b, b_vec.0[0])) == to_integer(at(remainder_lane_prefix, b_vec.0[0]));
     have to_integer(at(reduction_b, b_vec.0[1])) == to_integer(at(remainder_lane_prefix, b_vec.0[1]));
     have to_integer(at(reduction_b, b_vec.0[2])) == to_integer(at(remainder_lane_prefix, b_vec.0[2]));
     have to_integer(at(reduction_b, b_vec.0[3])) == to_integer(at(remainder_lane_prefix, b_vec.0[3]));
     step_until(assignment(__rust_mir_88, 0));
     have to_integer(__rust_checked_77) == to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76));
     have to_integer(__rust_checked_77) == to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)) by solve() using { to_integer(__rust_checked_77) == to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)); };
     have to_integer(__rust_checked_77) == to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)) by solve() using { to_integer(__rust_checked_77) == to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)); to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)) == to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)); to_integer(at(deferred_b, b)) == to_integer(at(remainder_lane_prefix, b)); to_integer(at(deferred_b, __rust_mir_76)) == to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)); };

     have 0 <= to_integer(__rust_checked_77);
     have to_integer(__rust_checked_77) <= 4294967295;
     have 0 <= to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)) by solve() using { 0 <= to_integer(__rust_checked_77); to_integer(__rust_checked_77) == to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)); };
     have 0 <= to_integer((at(remainder_lane_prefix, b_vec.0[0])));
     have to_integer((at(remainder_lane_prefix, b_vec.0[0]))) <= 4294967295;
     have 0 <= to_integer((at(remainder_lane_prefix, b_vec.0[1])));
     have to_integer((at(remainder_lane_prefix, b_vec.0[1]))) <= 4294967295;
     have 0 <= to_integer((at(remainder_lane_prefix, b_vec.0[2])));
     have to_integer((at(remainder_lane_prefix, b_vec.0[2]))) <= 4294967295;
     have 0 <= to_integer((at(remainder_lane_prefix, b_vec.0[3])));
     have to_integer((at(remainder_lane_prefix, b_vec.0[3]))) <= 4294967295;
     apply(adler_lane_b_reduction(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3])))) using { 0 <= to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[1])); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[2])); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[3])); 0 <= to_integer(at(remainder_lane_prefix, b_vec.0[0])); 0 <= to_integer(at(remainder_lane_prefix, b_vec.0[1])); 0 <= to_integer(at(remainder_lane_prefix, b_vec.0[2])); 0 <= to_integer(at(remainder_lane_prefix, b_vec.0[3])); 0 <= adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))); };
     have __rust_checked_82 == 65521u32;
     have 65521u32 == __rust_checked_82 by solve() using { __rust_checked_82 == 65521u32; };
     have b_vec.0[0] < __rust_checked_82;
     have b_vec.0[0] < 65521u32 by { rewrite(65521u32, __rust_checked_82); known(); }
     have b_vec.0[0] <= 4294967295u32 / 4u32 by solve() using { b_vec.0[0] < 65521u32; };
     have b_vec.0[1] < __rust_checked_82;
     have b_vec.0[1] < 65521u32 by { rewrite(65521u32, __rust_checked_82); known(); }
     have b_vec.0[1] <= 4294967295u32 / 4u32 by solve() using { b_vec.0[1] < 65521u32; };
     have b_vec.0[2] < __rust_checked_82;
     have b_vec.0[2] < 65521u32 by { rewrite(65521u32, __rust_checked_82); known(); }
     have b_vec.0[2] <= 4294967295u32 / 4u32 by solve() using { b_vec.0[2] < 65521u32; };
     have b_vec.0[3] < __rust_checked_82;
     have b_vec.0[3] < 65521u32 by { rewrite(65521u32, __rust_checked_82); known(); }
     have b_vec.0[3] <= 4294967295u32 / 4u32 by solve() using { b_vec.0[3] < 65521u32; };
     have to_integer(b_vec.0[0]) <= 65520 by solve() using { to_integer(b_vec.0[0]) < 65521; };
     have to_integer(b_vec.0[1]) <= 65520 by solve() using { to_integer(b_vec.0[1]) < 65521; };
     have to_integer(b_vec.0[2]) <= 65520 by solve() using { to_integer(b_vec.0[2]) < 65521; };
     have to_integer(b_vec.0[3]) <= 65520 by solve() using { to_integer(b_vec.0[3]) < 65521; };
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a));
     have __rust_checked_84 == 65521u32;
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % __rust_checked_84;
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32 by { rewrite(a_vec.0[0], at(reduction_a, a_vec.0[0]) % __rust_checked_84); solve() using { __rust_checked_84 == 65521u32; }; }
     have to_integer(65521u32) != 0 by { normalize(); }
     apply(integer::uint32_remainder_to_integer(at(reduction_a, a_vec.0[0]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(a_vec.0[0]) == to_integer(at(reduction_a, a_vec.0[0]) % 65521u32) by solve() using { a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[0]))); solve(); }
     have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521) by solve() using { to_integer(a_vec.0[0]) == to_integer(at(reduction_a, a_vec.0[0]) % 65521u32); to_integer(at(reduction_a, a_vec.0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521); };
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % __rust_checked_84;
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32 by { rewrite(a_vec.0[1], at(reduction_a, a_vec.0[1]) % __rust_checked_84); solve() using { __rust_checked_84 == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_a, a_vec.0[1]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(a_vec.0[1]) == to_integer(at(reduction_a, a_vec.0[1]) % 65521u32) by solve() using { a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[1]))); solve(); }
     have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521) by solve() using { to_integer(a_vec.0[1]) == to_integer(at(reduction_a, a_vec.0[1]) % 65521u32); to_integer(at(reduction_a, a_vec.0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521); };
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % __rust_checked_84;
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32 by { rewrite(a_vec.0[2], at(reduction_a, a_vec.0[2]) % __rust_checked_84); solve() using { __rust_checked_84 == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_a, a_vec.0[2]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(a_vec.0[2]) == to_integer(at(reduction_a, a_vec.0[2]) % 65521u32) by solve() using { a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[2]))); solve(); }
     have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521) by solve() using { to_integer(a_vec.0[2]) == to_integer(at(reduction_a, a_vec.0[2]) % 65521u32); to_integer(at(reduction_a, a_vec.0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521); };
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % __rust_checked_84;
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32 by { rewrite(a_vec.0[3], at(reduction_a, a_vec.0[3]) % __rust_checked_84); solve() using { __rust_checked_84 == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_a, a_vec.0[3]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(a_vec.0[3]) == to_integer(at(reduction_a, a_vec.0[3]) % 65521u32) by solve() using { a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[3])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))); solve(); }
     have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521) by solve() using { to_integer(a_vec.0[3]) == to_integer(at(reduction_a, a_vec.0[3]) % 65521u32); to_integer(at(reduction_a, a_vec.0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521); };
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(at(remainder_lane_prefix, a))) by { rewrite(to_integer(a), to_integer(at(remainder_lane_prefix, a))); rewrite(to_integer(a_vec.0[0]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521)); rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521)); rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521)); rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521)); solve() using { truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))), 65521) == truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521)), 65521); truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(at(remainder_lane_prefix, a))); }; }
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % __rust_checked_82;
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32 by { rewrite(b_vec.0[0], at(reduction_b, b_vec.0[0]) % __rust_checked_82); solve() using { __rust_checked_82 == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_b, b_vec.0[0]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(b_vec.0[0]) == to_integer(at(reduction_b, b_vec.0[0]) % 65521u32) by solve() using { b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[0]))); solve(); }
     have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521) by solve() using { to_integer(b_vec.0[0]) == to_integer(at(reduction_b, b_vec.0[0]) % 65521u32); to_integer(at(reduction_b, b_vec.0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521); };
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % __rust_checked_82;
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32 by { rewrite(b_vec.0[1], at(reduction_b, b_vec.0[1]) % __rust_checked_82); solve() using { __rust_checked_82 == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_b, b_vec.0[1]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(b_vec.0[1]) == to_integer(at(reduction_b, b_vec.0[1]) % 65521u32) by solve() using { b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[1]))); solve(); }
     have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521) by solve() using { to_integer(b_vec.0[1]) == to_integer(at(reduction_b, b_vec.0[1]) % 65521u32); to_integer(at(reduction_b, b_vec.0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521); };
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % __rust_checked_82;
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32 by { rewrite(b_vec.0[2], at(reduction_b, b_vec.0[2]) % __rust_checked_82); solve() using { __rust_checked_82 == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_b, b_vec.0[2]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(b_vec.0[2]) == to_integer(at(reduction_b, b_vec.0[2]) % 65521u32) by solve() using { b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[2]))); solve(); }
     have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521) by solve() using { to_integer(b_vec.0[2]) == to_integer(at(reduction_b, b_vec.0[2]) % 65521u32); to_integer(at(reduction_b, b_vec.0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521); };
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % __rust_checked_82;
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32 by { rewrite(b_vec.0[3], at(reduction_b, b_vec.0[3]) % __rust_checked_82); solve() using { __rust_checked_82 == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_b, b_vec.0[3]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(b_vec.0[3]) == to_integer(at(reduction_b, b_vec.0[3]) % 65521u32) by solve() using { b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))); solve(); }
     have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521) by solve() using { to_integer(b_vec.0[3]) == to_integer(at(reduction_b, b_vec.0[3]) % 65521u32); to_integer(at(reduction_b, b_vec.0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521); };
     have __rust_checked_79 == 65521u32;
     have b == __rust_checked_77 % __rust_checked_79;
     have b == __rust_checked_77 % 65521u32 by { rewrite(b, __rust_checked_77 % __rust_checked_79); solve() using { __rust_checked_79 == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(__rust_checked_77, 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(b) == to_integer(__rust_checked_77 % 65521u32) by solve() using { b == __rust_checked_77 % 65521u32; };
     have truncating_remainder(to_integer(__rust_checked_77), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521) by { rewrite(to_integer(__rust_checked_77), to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a))); solve(); }
     have to_integer(b) == truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521) by solve() using { to_integer(b) == to_integer(__rust_checked_77 % 65521u32); to_integer(__rust_checked_77 % 65521u32) == truncating_remainder(to_integer(__rust_checked_77), to_integer(65521u32)); truncating_remainder(to_integer(__rust_checked_77), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521); };
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521)); rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521)); rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521)); rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521)); rewrite(to_integer(b_vec.0[0]), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521)); rewrite(to_integer(b_vec.0[1]), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521)); rewrite(to_integer(b_vec.0[2]), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521)); rewrite(to_integer(b_vec.0[3]), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521)); solve() using { truncating_remainder(adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))), 65521) == truncating_remainder(adler_lane_b(truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521)), 65521); truncating_remainder(adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32)))); }; }
     mark weighted_b;
     have truncating_remainder(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32))));
     step_until(assignment(__rust_mir_91, 0));
     have __rust_checked_85 == 65521u32;
     have 65521u32 == __rust_checked_85 by solve() using { __rust_checked_85 == 65521u32; };
     have a_vec.0[0] < __rust_checked_85;
     have a_vec.0[0] < 65521u32 by { rewrite(65521u32, __rust_checked_85); known(); }
     have a_vec.0[1] < __rust_checked_85;
     have a_vec.0[1] < 65521u32 by { rewrite(65521u32, __rust_checked_85); known(); }
     have a_vec.0[2] < __rust_checked_85;
     have a_vec.0[2] < 65521u32 by { rewrite(65521u32, __rust_checked_85); known(); }
     have a_vec.0[3] < __rust_checked_85;
     have a_vec.0[3] < 65521u32 by { rewrite(65521u32, __rust_checked_85); known(); }
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have to_integer(at(weighted_b, b_vec.0[0])) <= 65520;
     have to_integer(b_vec.0[0]) <= 262080 by solve() using { to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4; to_integer(at(weighted_b, b_vec.0[0])) <= 65520; };
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(at(weighted_b, b_vec.0[1])) <= 65520;
     have to_integer(b_vec.0[1]) <= 262080 by solve() using { to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4; to_integer(at(weighted_b, b_vec.0[1])) <= 65520; };
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(at(weighted_b, b_vec.0[2])) <= 65520;
     have to_integer(b_vec.0[2]) <= 262080 by solve() using { to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4; to_integer(at(weighted_b, b_vec.0[2])) <= 65520; };
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(at(weighted_b, b_vec.0[3])) <= 65520;
     have to_integer(b_vec.0[3]) <= 262080 by solve() using { to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4; to_integer(at(weighted_b, b_vec.0[3])) <= 65520; };
     mark correction_b;
     have to_integer(at(correction_b, b_vec.0[1])) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(at(correction_b, a_vec.0[1])) == to_integer(at(weighted_b, a_vec.0[1]));
     have to_integer(at(correction_b, b_vec.0[2])) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(at(correction_b, a_vec.0[2])) == to_integer(at(weighted_b, a_vec.0[2]));
     have to_integer(at(correction_b, b_vec.0[3])) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(at(correction_b, a_vec.0[3])) == to_integer(at(weighted_b, a_vec.0[3]));
     apply(adler_recombine_lane_1(a_vec.0[1], b_vec.0[1])) using { a_vec.0[1] < 65521u32; to_integer(b_vec.0[1]) <= 262080; };
     apply(adler_recombine_lane_2(a_vec.0[2], b_vec.0[2])) using { a_vec.0[2] < 65521u32; to_integer(b_vec.0[2]) <= 262080; };
     apply(adler_recombine_lane_3(a_vec.0[3], b_vec.0[3])) using { a_vec.0[3] < 65521u32; to_integer(b_vec.0[3]) <= 262080; };
     apply(adler_recombine_difference(a_vec.0[2])) using { a_vec.0[2] < 65521u32; };
     have to_integer(65521u32 - a_vec.0[2]) <= to_integer(4294967295u32 / 2u32) by solve() using { to_integer(65521u32 - a_vec.0[2]) <= to_integer(65521u32); };
     apply(adler_recombine_difference(a_vec.0[3])) using { a_vec.0[3] < 65521u32; };
     have to_integer(65521u32 - a_vec.0[3]) <= to_integer(4294967295u32 / 3u32) by solve() using { to_integer(65521u32 - a_vec.0[3]) <= to_integer(65521u32); };
     have to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) == to_integer(at(correction_b, b_vec.0[1])) + (65521 - to_integer(at(correction_b, a_vec.0[1]))) * 1;
     have to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) == to_integer(at(correction_b, b_vec.0[2])) + (65521 - to_integer(at(correction_b, a_vec.0[2]))) * 2;
     have to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) == to_integer(at(correction_b, b_vec.0[3])) + (65521 - to_integer(at(correction_b, a_vec.0[3]))) * 3;
     step_until(assignment(__rust_mir_94, 0));
     have to_integer(__rust_mir_89) == to_integer((65521u32 - at(correction_b, a_vec.0[1])));
     have b_vec.0[1] == at(correction_b, b_vec.0[1]);
     mark correction_add_1;
     have to_integer(at(correction_add_1, __rust_mir_89)) == to_integer((65521u32 - at(correction_b, a_vec.0[1])));
     have at(correction_add_1, b_vec.0[1]) == at(correction_b, b_vec.0[1]);
     step();
     have to_integer(__rust_mir_94) == to_integer(at(correction_add_1, b_vec.0[1]) + at(correction_add_1, __rust_mir_89));
     have to_integer(__rust_mir_94) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) by { rewrite(to_integer(__rust_mir_94), to_integer(at(correction_add_1, b_vec.0[1]) + at(correction_add_1, __rust_mir_89))); rewrite(at(correction_add_1, b_vec.0[1]), at(correction_b, b_vec.0[1])); rewrite(to_integer(at(correction_add_1, __rust_mir_89)), to_integer((65521u32 - at(correction_b, a_vec.0[1])))); solve(); }
     mark correction_store_1;
     have to_integer(at(correction_store_1, __rust_mir_94)) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1])));
     step_until(assignment(__rust_mir_102, 0));
     have to_integer(__rust_mir_95) == to_integer(((65521u32 - at(correction_b, a_vec.0[2])) * 2u32));
     have b_vec.0[2] == at(correction_b, b_vec.0[2]);
     mark correction_add_2;
     have to_integer(at(correction_add_2, __rust_mir_95)) == to_integer(((65521u32 - at(correction_b, a_vec.0[2])) * 2u32));
     have at(correction_add_2, b_vec.0[2]) == at(correction_b, b_vec.0[2]);
     step();
     have to_integer(__rust_mir_102) == to_integer(at(correction_add_2, b_vec.0[2]) + at(correction_add_2, __rust_mir_95));
     have to_integer(__rust_mir_102) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) by { rewrite(to_integer(__rust_mir_102), to_integer(at(correction_add_2, b_vec.0[2]) + at(correction_add_2, __rust_mir_95))); rewrite(at(correction_add_2, b_vec.0[2]), at(correction_b, b_vec.0[2])); rewrite(to_integer(at(correction_add_2, __rust_mir_95)), to_integer(((65521u32 - at(correction_b, a_vec.0[2])) * 2u32))); solve(); }
     mark correction_store_2;
     have to_integer(at(correction_store_2, __rust_mir_102)) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32));
     step_until(assignment(__rust_mir_104, 0)); step();
     have to_integer(__rust_mir_104) == to_integer(65521u32 - at(correction_b, a_vec.0[3]));
     step_until(assignment(__rust_mir_108, 0));
     mark correction_multiply_3;
     have to_integer(at(correction_multiply_3, __rust_mir_104)) == to_integer(65521u32 - at(correction_b, a_vec.0[3]));
     step();
     have to_integer(__rust_mir_108) == to_integer(at(correction_multiply_3, __rust_mir_104) * 3u32);
     have to_integer(__rust_mir_108) == to_integer((65521u32 - at(correction_b, a_vec.0[3])) * 3u32) by { rewrite(to_integer(__rust_mir_108), to_integer(at(correction_multiply_3, __rust_mir_104) * 3u32)); rewrite(to_integer(at(correction_multiply_3, __rust_mir_104)), to_integer(65521u32 - at(correction_b, a_vec.0[3]))); solve(); }
     step_until(assignment(__rust_mir_103, 0)); step();
     have to_integer(__rust_mir_103) == to_integer((65521u32 - at(correction_b, a_vec.0[3])) * 3u32) by solve() using { to_integer(__rust_mir_108) == to_integer((65521u32 - at(correction_b, a_vec.0[3])) * 3u32); };
     step_until(assignment(__rust_mir_110, 0));
     have b_vec.0[3] == at(correction_b, b_vec.0[3]);
     mark correction_add_3;
     have to_integer(at(correction_add_3, __rust_mir_103)) == to_integer(((65521u32 - at(correction_b, a_vec.0[3])) * 3u32));
     have at(correction_add_3, b_vec.0[3]) == at(correction_b, b_vec.0[3]);
     step();
     have to_integer(__rust_mir_110) == to_integer(at(correction_add_3, b_vec.0[3]) + at(correction_add_3, __rust_mir_103));
     have to_integer(__rust_mir_110) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) by { rewrite(to_integer(__rust_mir_110), to_integer(at(correction_add_3, b_vec.0[3]) + at(correction_add_3, __rust_mir_103))); rewrite(at(correction_add_3, b_vec.0[3]), at(correction_b, b_vec.0[3])); rewrite(to_integer(at(correction_add_3, __rust_mir_103)), to_integer(((65521u32 - at(correction_b, a_vec.0[3])) * 3u32))); solve(); }
     mark correction_store_3;
     have to_integer(at(correction_store_3, __rust_mir_110)) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32));
     step_until(loop(3));
     have b_vec.0[1] == at(correction_store_1, __rust_mir_94);
     have to_integer(b_vec.0[1]) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) by { rewrite(b_vec.0[1], at(correction_store_1, __rust_mir_94)); rewrite(to_integer(at(correction_store_1, __rust_mir_94)), to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1])))); solve(); }
     have to_integer(b_vec.0[1]) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) by solve() using { to_integer(b_vec.0[1]) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))); };
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[1]))) * 1 by solve() using { to_integer(b_vec.0[1]) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))); to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) == to_integer(at(correction_b, b_vec.0[1])) + (65521 - to_integer(at(correction_b, a_vec.0[1]))) * 1; to_integer(at(correction_b, b_vec.0[1])) == to_integer(at(weighted_b, b_vec.0[1])) * 4; to_integer(at(correction_b, a_vec.0[1])) == to_integer(at(weighted_b, a_vec.0[1])); };
     have b_vec.0[2] == at(correction_store_2, __rust_mir_102);
     have to_integer(b_vec.0[2]) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) by { rewrite(b_vec.0[2], at(correction_store_2, __rust_mir_102)); rewrite(to_integer(at(correction_store_2, __rust_mir_102)), to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32))); solve(); }
     have to_integer(b_vec.0[2]) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) by solve() using { to_integer(b_vec.0[2]) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)); };
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[2]))) * 2 by solve() using { to_integer(b_vec.0[2]) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)); to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) == to_integer(at(correction_b, b_vec.0[2])) + (65521 - to_integer(at(correction_b, a_vec.0[2]))) * 2; to_integer(at(correction_b, b_vec.0[2])) == to_integer(at(weighted_b, b_vec.0[2])) * 4; to_integer(at(correction_b, a_vec.0[2])) == to_integer(at(weighted_b, a_vec.0[2])); };
     have b_vec.0[3] == at(correction_store_3, __rust_mir_110);
     have to_integer(b_vec.0[3]) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) by { rewrite(b_vec.0[3], at(correction_store_3, __rust_mir_110)); rewrite(to_integer(at(correction_store_3, __rust_mir_110)), to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32))); solve(); }
     have to_integer(b_vec.0[3]) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) by solve() using { to_integer(b_vec.0[3]) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)); };
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[3]))) * 3 by solve() using { to_integer(b_vec.0[3]) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)); to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) == to_integer(at(correction_b, b_vec.0[3])) + (65521 - to_integer(at(correction_b, a_vec.0[3]))) * 3; to_integer(at(correction_b, b_vec.0[3])) == to_integer(at(weighted_b, b_vec.0[3])) * 4; to_integer(at(correction_b, a_vec.0[3])) == to_integer(at(weighted_b, a_vec.0[3])); };
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have a <= 65520u32 by known();
     step_until(assignment(__rust_mir_121, 0));
     have av == a_vec.0[0];
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[0]); solve() using { to_integer(a_vec.0[0]) < 65521; }; }
     step();
     have to_integer(__rust_mir_121) <= 65520 by solve() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by solve() using { to_integer(a) <= 65520; to_integer(__rust_mir_121) <= 65520; };
     have a <= 4294967295u32 - __rust_mir_121 by solve() using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; };
     step_until(assignment(__rust_mir_122, 0));
     mark remainder_sum_a_0;
     have to_integer(at(remainder_sum_a_0, a)) == to_integer(at(remainder_lane_prefix, a));
     have to_integer(at(remainder_sum_a_0, __rust_mir_121)) == to_integer(a_vec.0[0]);
     have to_integer(at(remainder_sum_a_0, a)) <= 65520 by solve() using { to_integer(a) <= 65520; };
     have to_integer(at(remainder_sum_a_0, __rust_mir_121)) <= 65520 by solve() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)) <= 4294967295 by solve() using { to_integer(at(remainder_sum_a_0, a)) <= 65520; to_integer(at(remainder_sum_a_0, __rust_mir_121)) <= 65520; };
     step();
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121));
     have to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121)) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)) by apply(integer::uint32_add_to_integer(at(remainder_sum_a_0, a), at(remainder_sum_a_0, __rust_mir_121))) using { to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)) <= 4294967295; };
     have to_integer(__rust_mir_122) <= 131040 by { rewrite(to_integer(__rust_mir_122), to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121))); rewrite(to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121)), to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121))); solve() using { to_integer(at(remainder_sum_a_0, a)) <= 65520; to_integer(at(remainder_sum_a_0, __rust_mir_121)) <= 65520; }; }
     step_until(assignment(a, 1)); step();
     have to_integer(a) <= 131040 by solve() using { to_integer(__rust_mir_122) <= 131040; };
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)) by solve() using { to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121)); to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121)) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) by solve() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)); to_integer(at(remainder_sum_a_0, a)) == to_integer(at(remainder_lane_prefix, a)); to_integer(at(remainder_sum_a_0, __rust_mir_121)) == to_integer(a_vec.0[0]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     step_until(assignment(__rust_mir_121, 0));
     have av == a_vec.0[1];
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[1]); solve() using { to_integer(a_vec.0[1]) < 65521; }; }
     step();
     have to_integer(__rust_mir_121) <= 65520 by solve() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by solve() using { to_integer(a) <= 131040; to_integer(__rust_mir_121) <= 65520; };
     have a <= 4294967295u32 - __rust_mir_121 by solve() using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; };
     step_until(assignment(__rust_mir_122, 0));
     mark remainder_sum_a_1;
     have to_integer(at(remainder_sum_a_1, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]);
     have to_integer(at(remainder_sum_a_1, __rust_mir_121)) == to_integer(a_vec.0[1]);
     have to_integer(at(remainder_sum_a_1, a)) <= 131040 by solve() using { to_integer(a) <= 131040; };
     have to_integer(at(remainder_sum_a_1, __rust_mir_121)) <= 65520 by solve() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)) <= 4294967295 by solve() using { to_integer(at(remainder_sum_a_1, a)) <= 131040; to_integer(at(remainder_sum_a_1, __rust_mir_121)) <= 65520; };
     step();
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121));
     have to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121)) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)) by apply(integer::uint32_add_to_integer(at(remainder_sum_a_1, a), at(remainder_sum_a_1, __rust_mir_121))) using { to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)) <= 4294967295; };
     have to_integer(__rust_mir_122) <= 196560 by { rewrite(to_integer(__rust_mir_122), to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121))); rewrite(to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121)), to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121))); solve() using { to_integer(at(remainder_sum_a_1, a)) <= 131040; to_integer(at(remainder_sum_a_1, __rust_mir_121)) <= 65520; }; }
     step_until(assignment(a, 1)); step();
     have to_integer(a) <= 196560 by solve() using { to_integer(__rust_mir_122) <= 196560; };
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)) by solve() using { to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121)); to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121)) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) by solve() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)); to_integer(at(remainder_sum_a_1, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]); to_integer(at(remainder_sum_a_1, __rust_mir_121)) == to_integer(a_vec.0[1]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     step_until(assignment(__rust_mir_121, 0));
     have av == a_vec.0[2];
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[2]); solve() using { to_integer(a_vec.0[2]) < 65521; }; }
     step();
     have to_integer(__rust_mir_121) <= 65520 by solve() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by solve() using { to_integer(a) <= 196560; to_integer(__rust_mir_121) <= 65520; };
     have a <= 4294967295u32 - __rust_mir_121 by solve() using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; };
     step_until(assignment(__rust_mir_122, 0));
     mark remainder_sum_a_2;
     have to_integer(at(remainder_sum_a_2, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]);
     have to_integer(at(remainder_sum_a_2, __rust_mir_121)) == to_integer(a_vec.0[2]);
     have to_integer(at(remainder_sum_a_2, a)) <= 196560 by solve() using { to_integer(a) <= 196560; };
     have to_integer(at(remainder_sum_a_2, __rust_mir_121)) <= 65520 by solve() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)) <= 4294967295 by solve() using { to_integer(at(remainder_sum_a_2, a)) <= 196560; to_integer(at(remainder_sum_a_2, __rust_mir_121)) <= 65520; };
     step();
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121));
     have to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121)) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)) by apply(integer::uint32_add_to_integer(at(remainder_sum_a_2, a), at(remainder_sum_a_2, __rust_mir_121))) using { to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)) <= 4294967295; };
     have to_integer(__rust_mir_122) <= 262080 by { rewrite(to_integer(__rust_mir_122), to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121))); rewrite(to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121)), to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121))); solve() using { to_integer(at(remainder_sum_a_2, a)) <= 196560; to_integer(at(remainder_sum_a_2, __rust_mir_121)) <= 65520; }; }
     step_until(assignment(a, 1)); step();
     have to_integer(a) <= 262080 by solve() using { to_integer(__rust_mir_122) <= 262080; };
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)) by solve() using { to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121)); to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121)) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) by solve() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)); to_integer(at(remainder_sum_a_2, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]); to_integer(at(remainder_sum_a_2, __rust_mir_121)) == to_integer(a_vec.0[2]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     step_until(assignment(__rust_mir_121, 0));
     have av == a_vec.0[3];
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[3]); solve() using { to_integer(a_vec.0[3]) < 65521; }; }
     step();
     have to_integer(__rust_mir_121) <= 65520 by solve() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by solve() using { to_integer(a) <= 262080; to_integer(__rust_mir_121) <= 65520; };
     have a <= 4294967295u32 - __rust_mir_121 by solve() using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; };
     step_until(assignment(__rust_mir_122, 0));
     mark remainder_sum_a_3;
     have to_integer(at(remainder_sum_a_3, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]);
     have to_integer(at(remainder_sum_a_3, __rust_mir_121)) == to_integer(a_vec.0[3]);
     have to_integer(at(remainder_sum_a_3, a)) <= 262080 by solve() using { to_integer(a) <= 262080; };
     have to_integer(at(remainder_sum_a_3, __rust_mir_121)) <= 65520 by solve() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)) <= 4294967295 by solve() using { to_integer(at(remainder_sum_a_3, a)) <= 262080; to_integer(at(remainder_sum_a_3, __rust_mir_121)) <= 65520; };
     step();
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121));
     have to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121)) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)) by apply(integer::uint32_add_to_integer(at(remainder_sum_a_3, a), at(remainder_sum_a_3, __rust_mir_121))) using { to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)) <= 4294967295; };
     have to_integer(__rust_mir_122) <= 327600 by { rewrite(to_integer(__rust_mir_122), to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121))); rewrite(to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121)), to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121))); solve() using { to_integer(at(remainder_sum_a_3, a)) <= 262080; to_integer(at(remainder_sum_a_3, __rust_mir_121)) <= 65520; }; }
     step_until(assignment(a, 1)); step();
     have to_integer(a) <= 327600 by solve() using { to_integer(__rust_mir_122) <= 327600; };
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)) by solve() using { to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121)); to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121)) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) + to_integer(a_vec.0[3]) by solve() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)); to_integer(at(remainder_sum_a_3, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]); to_integer(at(remainder_sum_a_3, __rust_mir_121)) == to_integer(a_vec.0[3]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(a) == adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) by { unfold(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); known(); }
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(at(remainder_lane_prefix, a))) by { rewrite(to_integer(a), adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); known(); }
     step_until(loop(4));
     have __rust_checked_79 == 65521u32;
     have 65521u32 == __rust_checked_79 by solve() using { __rust_checked_79 == 65521u32; };
     have b == __rust_checked_77 % __rust_checked_79;
     have __rust_checked_79 != 0u32 by { rewrite(__rust_checked_79, 65521u32); normalize(); }
     apply(integer::uint32_remainder_less_than_divisor(__rust_checked_77, __rust_checked_79)) using { __rust_checked_79 != 0u32; };
     have b < __rust_checked_79 by { rewrite(b, __rust_checked_77 % __rust_checked_79); known(); }
     have b < 65521u32 by { rewrite(65521u32, __rust_checked_79); known(); }
     have to_integer(b) <= 65520 by solve() using { to_integer(b) < 65521; };
     have to_integer(b_vec.0[0]) <= 262080;
     step_until(assignment(__rust_mir_133, 0));
     have bv == b_vec.0[0];
     have to_integer(bv) <= 262080 by { rewrite(bv, b_vec.0[0]); known(); }
     step();
     have to_integer(__rust_mir_133) <= 262080 by solve() using { to_integer(bv) <= 262080; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by solve() using { to_integer(b) <= 65520; to_integer(__rust_mir_133) <= 262080; };
     have b <= 4294967295u32 - __rust_mir_133 by solve() using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; };
     step_until(assignment(__rust_mir_134, 0));
     mark remainder_sum_b_0;
     have to_integer(at(remainder_sum_b_0, b)) == to_integer(at(weighted_b, b));
     have to_integer(at(remainder_sum_b_0, __rust_mir_133)) == to_integer(b_vec.0[0]);
     have to_integer(at(remainder_sum_b_0, b)) <= 65520 by solve() using { to_integer(b) <= 65520; };
     have to_integer(at(remainder_sum_b_0, __rust_mir_133)) <= 262080 by solve() using { to_integer(__rust_mir_133) <= 262080; };
     have to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)) <= 4294967295 by solve() using { to_integer(at(remainder_sum_b_0, b)) <= 65520; to_integer(at(remainder_sum_b_0, __rust_mir_133)) <= 262080; };
     step();
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133));
     have to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133)) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)) by apply(integer::uint32_add_to_integer(at(remainder_sum_b_0, b), at(remainder_sum_b_0, __rust_mir_133))) using { to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)) <= 4294967295; };
     have to_integer(__rust_mir_134) <= 327600 by { rewrite(to_integer(__rust_mir_134), to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133))); rewrite(to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133)), to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133))); solve() using { to_integer(at(remainder_sum_b_0, b)) <= 65520; to_integer(at(remainder_sum_b_0, __rust_mir_133)) <= 262080; }; }
     step_until(assignment(b, 5)); step();
     have to_integer(b) <= 327600 by solve() using { to_integer(__rust_mir_134) <= 327600; };
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)) by solve() using { to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133)); to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133)) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) by solve() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)); to_integer(at(remainder_sum_b_0, b)) == to_integer(at(weighted_b, b)); to_integer(at(remainder_sum_b_0, __rust_mir_133)) == to_integer(b_vec.0[0]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(b_vec.0[1]) <= 327601;
     step_until(assignment(__rust_mir_133, 0));
     have bv == b_vec.0[1];
     have to_integer(bv) <= 327601 by { rewrite(bv, b_vec.0[1]); known(); }
     step();
     have to_integer(__rust_mir_133) <= 327601 by solve() using { to_integer(bv) <= 327601; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by solve() using { to_integer(b) <= 327600; to_integer(__rust_mir_133) <= 327601; };
     have b <= 4294967295u32 - __rust_mir_133 by solve() using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; };
     step_until(assignment(__rust_mir_134, 0));
     mark remainder_sum_b_1;
     have to_integer(at(remainder_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]);
     have to_integer(at(remainder_sum_b_1, __rust_mir_133)) == to_integer(b_vec.0[1]);
     have to_integer(at(remainder_sum_b_1, b)) <= 327600 by solve() using { to_integer(b) <= 327600; };
     have to_integer(at(remainder_sum_b_1, __rust_mir_133)) <= 327601 by solve() using { to_integer(__rust_mir_133) <= 327601; };
     have to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)) <= 4294967295 by solve() using { to_integer(at(remainder_sum_b_1, b)) <= 327600; to_integer(at(remainder_sum_b_1, __rust_mir_133)) <= 327601; };
     step();
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133));
     have to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133)) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)) by apply(integer::uint32_add_to_integer(at(remainder_sum_b_1, b), at(remainder_sum_b_1, __rust_mir_133))) using { to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)) <= 4294967295; };
     have to_integer(__rust_mir_134) <= 655201 by { rewrite(to_integer(__rust_mir_134), to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133))); rewrite(to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133)), to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133))); solve() using { to_integer(at(remainder_sum_b_1, b)) <= 327600; to_integer(at(remainder_sum_b_1, __rust_mir_133)) <= 327601; }; }
     step_until(assignment(b, 5)); step();
     have to_integer(b) <= 655201 by solve() using { to_integer(__rust_mir_134) <= 655201; };
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)) by solve() using { to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133)); to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133)) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) by solve() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)); to_integer(at(remainder_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]); to_integer(at(remainder_sum_b_1, __rust_mir_133)) == to_integer(b_vec.0[1]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(b_vec.0[2]) <= 393122;
     step_until(assignment(__rust_mir_133, 0));
     have bv == b_vec.0[2];
     have to_integer(bv) <= 393122 by { rewrite(bv, b_vec.0[2]); known(); }
     step();
     have to_integer(__rust_mir_133) <= 393122 by solve() using { to_integer(bv) <= 393122; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by solve() using { to_integer(b) <= 655201; to_integer(__rust_mir_133) <= 393122; };
     have b <= 4294967295u32 - __rust_mir_133 by solve() using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; };
     step_until(assignment(__rust_mir_134, 0));
     mark remainder_sum_b_2;
     have to_integer(at(remainder_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]);
     have to_integer(at(remainder_sum_b_2, __rust_mir_133)) == to_integer(b_vec.0[2]);
     have to_integer(at(remainder_sum_b_2, b)) <= 655201 by solve() using { to_integer(b) <= 655201; };
     have to_integer(at(remainder_sum_b_2, __rust_mir_133)) <= 393122 by solve() using { to_integer(__rust_mir_133) <= 393122; };
     have to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)) <= 4294967295 by solve() using { to_integer(at(remainder_sum_b_2, b)) <= 655201; to_integer(at(remainder_sum_b_2, __rust_mir_133)) <= 393122; };
     step();
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133));
     have to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133)) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)) by apply(integer::uint32_add_to_integer(at(remainder_sum_b_2, b), at(remainder_sum_b_2, __rust_mir_133))) using { to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)) <= 4294967295; };
     have to_integer(__rust_mir_134) <= 1048323 by { rewrite(to_integer(__rust_mir_134), to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133))); rewrite(to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133)), to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133))); solve() using { to_integer(at(remainder_sum_b_2, b)) <= 655201; to_integer(at(remainder_sum_b_2, __rust_mir_133)) <= 393122; }; }
     step_until(assignment(b, 5)); step();
     have to_integer(b) <= 1048323 by solve() using { to_integer(__rust_mir_134) <= 1048323; };
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)) by solve() using { to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133)); to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133)) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) by solve() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)); to_integer(at(remainder_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]); to_integer(at(remainder_sum_b_2, __rust_mir_133)) == to_integer(b_vec.0[2]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(b_vec.0[3]) <= 458643;
     step_until(assignment(__rust_mir_133, 0));
     have bv == b_vec.0[3];
     have to_integer(bv) <= 458643 by { rewrite(bv, b_vec.0[3]); known(); }
     step();
     have to_integer(__rust_mir_133) <= 458643 by solve() using { to_integer(bv) <= 458643; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by solve() using { to_integer(b) <= 1048323; to_integer(__rust_mir_133) <= 458643; };
     have b <= 4294967295u32 - __rust_mir_133 by solve() using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; };
     step_until(assignment(__rust_mir_134, 0));
     mark remainder_sum_b_3;
     have to_integer(at(remainder_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]);
     have to_integer(at(remainder_sum_b_3, __rust_mir_133)) == to_integer(b_vec.0[3]);
     have to_integer(at(remainder_sum_b_3, b)) <= 1048323 by solve() using { to_integer(b) <= 1048323; };
     have to_integer(at(remainder_sum_b_3, __rust_mir_133)) <= 458643 by solve() using { to_integer(__rust_mir_133) <= 458643; };
     have to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)) <= 4294967295 by solve() using { to_integer(at(remainder_sum_b_3, b)) <= 1048323; to_integer(at(remainder_sum_b_3, __rust_mir_133)) <= 458643; };
     step();
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133));
     have to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133)) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)) by apply(integer::uint32_add_to_integer(at(remainder_sum_b_3, b), at(remainder_sum_b_3, __rust_mir_133))) using { to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)) <= 4294967295; };
     have to_integer(__rust_mir_134) <= 1506966 by { rewrite(to_integer(__rust_mir_134), to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133))); rewrite(to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133)), to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133))); solve() using { to_integer(at(remainder_sum_b_3, b)) <= 1048323; to_integer(at(remainder_sum_b_3, __rust_mir_133)) <= 458643; }; }
     step_until(assignment(b, 5)); step();
     have to_integer(b) <= 1506966 by solve() using { to_integer(__rust_mir_134) <= 1506966; };
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)) by solve() using { to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133)); to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133)) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) + to_integer(b_vec.0[3]) by solve() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)); to_integer(at(remainder_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]); to_integer(at(remainder_sum_b_3, __rust_mir_133)) == to_integer(b_vec.0[3]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have remainder_len == bytes.len() % 4u64 by known();
     apply(adler_general_tail_metadata_u64(bytes.len()));
     have remainder_len <= 3u64 by { rewrite(remainder_len, bytes.len() % 4u64); known(); }
     have remainder_len <= 2147483647u64 by normalize() using { remainder_len <= 3u64; };

     have to_integer(b) == adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))) by { unfold(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3])))); solve() using { to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) + to_integer(b_vec.0[3]); to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4; to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[1]))) * 1; to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[2]))) * 2; to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[3]))) * 3; }; }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes, (bytes.len() - bytes.len() % 4u64), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3])))); known(); }
     step_until(loop(5));
     apply(adler_bounded_count(remainder_len));
     apply(adler_bounded_count_upper(remainder_len, 3));
     have 0 <= ((remainder_len as u32) as i32);
     have ((remainder_len as u32) as i32) <= 3;
     have ((__rust_mir_138_remaining as u32) as i32) == ((remainder_len as u32) as i32) by solve() using { remainder_len <= 3u64; };
     have 0 <= ((__rust_mir_138_remaining as u32) as i32) and ((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32) by { rewrite(((__rust_mir_138_remaining as u32) as i32), ((remainder_len as u32) as i32)); both { known(); } and { normalize() using {}; } }
     have __rust_mir_138_base == remainder;
     have __rust_mir_138_length == remainder_len;
     have adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)) == 0 by { unfold(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))); rewrite(((__rust_mir_138_remaining as u32) as i32), ((remainder_len as u32) as i32)); solve() using {}; }
     have adler_tail_a_ceiling(0) == 327600 by { unfold(adler_tail_a_ceiling(0)); normalize() using {}; }
     have adler_tail_b_ceiling(0) == 1506966 by { unfold(adler_tail_b_ceiling(0)); normalize() using {}; }
     have 0 <= to_integer(a);
     have to_integer(a) <= 4294967295;
     have 0 <= to_integer(b);
     have to_integer(b) <= 4294967295;
     have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)), 0); rewrite(adler_tail_a_ceiling(0), 327600); known(); }
     have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)), 0); rewrite(adler_tail_b_ceiling(0), 1506966); known(); }
     have remainder_len <= bytes.len() by { rewrite(remainder_len, bytes.len() % 4u64); normalize(); }
     have __rust_mir_138_remaining == remainder_len;
     have __rust_mir_138_remaining <= remainder_len by { rewrite(__rust_mir_138_remaining, remainder_len); normalize(); }
     have remainder == bytes + (bytes.len() - bytes.len() % 4u64);
     have to_integer(bytes.len() - __rust_mir_138_remaining) == to_integer(bytes.len() - bytes.len() % 4u64) by { rewrite(__rust_mir_138_remaining, remainder_len); rewrite(remainder_len, bytes.len() % 4u64); normalize(); }
     have __rust_mir_138_base == bytes + (bytes.len() - bytes.len() % 4u64) by solve() using { __rust_mir_138_base == remainder; remainder == bytes + (bytes.len() - bytes.len() % 4u64); };
     have remainder_len == bytes.len() % 4u64;
     have __rust_mir_138_remaining <= 3u64;
     // Connect the completed aligned prefix to the actual scalar iterator.
     have old(to_integer((self.a as u32))) == to_integer(at(remainder_lane_prefix, a));
     have 0 <= to_integer((old((self.a as u32))));
     have to_integer((old((self.a as u32)))) <= 4294967295;
     have to_integer((old((self.a as u32)))) <= to_integer(65520u32);
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes, bytes.len() - __rust_mir_138_remaining, old(to_integer((self.a as u32)))) by { rewrite(to_integer(bytes.len() - __rust_mir_138_remaining), to_integer(bytes.len() - bytes.len() % 4u64)); rewrite(old(to_integer((self.a as u32))), to_integer(at(remainder_lane_prefix, a))); known(); }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes, bytes.len() - __rust_mir_138_remaining, old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(bytes.len() - __rust_mir_138_remaining), to_integer(bytes.len() - bytes.len() % 4u64)); rewrite(old(to_integer((self.a as u32))), to_integer(at(remainder_lane_prefix, a))); known(); }
     loop {
      decreases __rust_mir_138_remaining;
      views *bytes;
      invariant bytes.len() == old(bytes.len());
      invariant bytes == old(bytes);
      invariant forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
      invariant 0 <= ((remainder_len as u32) as i32) and ((remainder_len as u32) as i32) <= 3;
      invariant 0 <= ((__rust_mir_138_remaining as u32) as i32) and ((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32);
       invariant remainder_len <= 3u64;
       invariant remainder_len <= bytes.len();
       invariant __rust_mir_138_remaining <= remainder_len;
       invariant __rust_mir_138_base == bytes + (bytes.len() - bytes.len() % 4u64);
       invariant __rust_mir_138_length == remainder_len;
       invariant remainder_len == bytes.len() % 4u64;
      invariant 0 <= old(to_integer((self.a as u32))) and old(to_integer((self.a as u32))) <= 65520;
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes, bytes.len() - __rust_mir_138_remaining, old(to_integer((self.a as u32))));
      invariant truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes, bytes.len() - __rust_mir_138_remaining, old(to_integer((self.a as u32))), old(to_integer((self.b as u32))));
      invariant 0 <= to_integer(a) and to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)));
      invariant 0 <= to_integer(b) and to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)));
      preserve by {
        have 0u64 < __rust_mir_138_remaining;
        have 1u64 <= __rust_mir_138_remaining by solve() using { 0u64 < __rust_mir_138_remaining; };
        have __rust_mir_138_remaining <= 22208u64 by solve() using { __rust_mir_138_remaining <= remainder_len; remainder_len <= 3u64; };
        apply(adler_count_tail_step(__rust_mir_138_remaining)) using { 1u64 <= __rust_mir_138_remaining; __rust_mir_138_remaining <= 22208u64; };
        have 0 < ((__rust_mir_138_remaining as u32) as i32) by solve() using { 1 <= ((__rust_mir_138_remaining as u32) as i32); };
       have 1 <= ((__rust_mir_138_remaining as u32) as i32) by solve() using { 0 < ((__rust_mir_138_remaining as u32) as i32); };
       have 0 <= to_integer(((__rust_mir_138_remaining as u32) as i32) - 1) by solve() using { 0 < ((__rust_mir_138_remaining as u32) as i32); };
       have to_integer(((__rust_mir_138_remaining as u32) as i32) - 1) <= to_integer(((remainder_len as u32) as i32)) by solve() using { 0 < ((__rust_mir_138_remaining as u32) as i32); ((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32); };
       mark tail_head;
       have 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32));
       have at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((remainder_len as u32) as i32);
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))));
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))));
        have 1u64 <= at(tail_head, __rust_mir_138_remaining);
        have at(tail_head, __rust_mir_138_remaining) <= remainder_len;
        have to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining)) < to_integer(bytes.len()) by solve() using { 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have truncating_remainder(to_integer(at(tail_head, a)), 65521) == adler_spec_a_u64(bytes, bytes.len() - at(tail_head, __rust_mir_138_remaining), old(to_integer((self.a as u32))));
       have truncating_remainder(to_integer(at(tail_head, b)), 65521) == adler_spec_b_u64(bytes, bytes.len() - at(tail_head, __rust_mir_138_remaining), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))));
        have bytes.len() % 4u64 <= bytes.len() by normalize();
        apply(integer::uint64_subtract_to_integer(bytes.len(), bytes.len() % 4u64));
        have to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(bytes.len()) by solve() using { to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64); };
        have bytes.len() - bytes.len() % 4u64 <= bytes.len() by solve() using { to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(bytes.len()); };
        apply(integer::uint64_subtract_to_integer(bytes.len(), bytes.len() - bytes.len() % 4u64));
        have to_integer(remainder_len) == to_integer(bytes.len() - (bytes.len() - bytes.len() % 4u64)) by solve() using { to_integer(bytes.len() - (bytes.len() - bytes.len() % 4u64)) == to_integer(bytes.len()) - to_integer(bytes.len() - bytes.len() % 4u64); to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64); remainder_len == bytes.len() % 4u64; };
        apply(adler_tail_read_offset(bytes.len() - bytes.len() % 4u64, bytes.len(), remainder_len, __rust_mir_138_remaining)) using { to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(bytes.len()); to_integer(remainder_len) == to_integer(bytes.len() - (bytes.len() - bytes.len() % 4u64)); 1u64 <= __rust_mir_138_remaining; __rust_mir_138_remaining <= remainder_len; };
       step_until(assignment(byte, 0));
        // The element this pass yields is `remaining` elements before the end of the scalar tail.
        have __rust_mir_155 == __rust_mir_138_base + (remainder_len - at(tail_head, __rust_mir_138_remaining));
        have __rust_mir_155 == bytes + (bytes.len() - at(tail_head, __rust_mir_138_remaining)) by {
         apply(integer::uint64_subtract_to_integer(remainder_len, at(tail_head, __rust_mir_138_remaining)));
         have to_integer(at(tail_head, __rust_mir_138_remaining)) <= to_integer(bytes.len()) by solve() using { at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
         apply(integer::uint64_subtract_to_integer(bytes.len(), at(tail_head, __rust_mir_138_remaining)));
         have bytes.len() % 4u64 <= bytes.len() by normalize();
         apply(integer::uint64_subtract_to_integer(bytes.len(), bytes.len() % 4u64));
         have to_integer(remainder_len) == to_integer(bytes.len() % 4u64) by solve() using { remainder_len == bytes.len() % 4u64; };
         have to_integer((bytes.len() - bytes.len() % 4u64)) + to_integer((remainder_len - at(tail_head, __rust_mir_138_remaining))) == to_integer((bytes.len() - at(tail_head, __rust_mir_138_remaining))) by solve() using { to_integer(remainder_len - at(tail_head, __rust_mir_138_remaining)) == to_integer(remainder_len) - to_integer(at(tail_head, __rust_mir_138_remaining)); to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining)) == to_integer(bytes.len()) - to_integer(at(tail_head, __rust_mir_138_remaining)); to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64); to_integer(remainder_len) == to_integer(bytes.len() % 4u64); };
         have to_integer((bytes.len() - at(tail_head, __rust_mir_138_remaining))) <= 18446744073709551615;
         have to_integer((bytes.len() - bytes.len() % 4u64)) + to_integer((remainder_len - at(tail_head, __rust_mir_138_remaining))) <= 18446744073709551615 by solve() using { to_integer((bytes.len() - bytes.len() % 4u64)) + to_integer((remainder_len - at(tail_head, __rust_mir_138_remaining))) == to_integer((bytes.len() - at(tail_head, __rust_mir_138_remaining))); to_integer((bytes.len() - at(tail_head, __rust_mir_138_remaining))) <= 18446744073709551615; };
         apply(integer::uint64_add_to_integer((bytes.len() - bytes.len() % 4u64), (remainder_len - at(tail_head, __rust_mir_138_remaining))));
         have __rust_mir_138_base + (remainder_len - at(tail_head, __rust_mir_138_remaining)) == bytes + ((bytes.len() - bytes.len() % 4u64) + (remainder_len - at(tail_head, __rust_mir_138_remaining))) by { rewrite(__rust_mir_138_base, bytes + (bytes.len() - bytes.len() % 4u64)); solve() using { to_integer((bytes.len() - bytes.len() % 4u64)) + to_integer((remainder_len - at(tail_head, __rust_mir_138_remaining))) <= 18446744073709551615; to_integer((bytes.len() - bytes.len() % 4u64) + (remainder_len - at(tail_head, __rust_mir_138_remaining))) == to_integer((bytes.len() - bytes.len() % 4u64)) + to_integer((remainder_len - at(tail_head, __rust_mir_138_remaining))); }; }
         have to_integer((bytes.len() - at(tail_head, __rust_mir_138_remaining))) == to_integer((bytes.len() - bytes.len() % 4u64) + (remainder_len - at(tail_head, __rust_mir_138_remaining))) by solve() using { to_integer((bytes.len() - bytes.len() % 4u64) + (remainder_len - at(tail_head, __rust_mir_138_remaining))) == to_integer((bytes.len() - bytes.len() % 4u64)) + to_integer((remainder_len - at(tail_head, __rust_mir_138_remaining))); to_integer((bytes.len() - bytes.len() % 4u64)) + to_integer((remainder_len - at(tail_head, __rust_mir_138_remaining))) == to_integer((bytes.len() - at(tail_head, __rust_mir_138_remaining))); };
         rewrite(to_integer((bytes.len() - at(tail_head, __rust_mir_138_remaining))), to_integer((bytes.len() - bytes.len() % 4u64) + (remainder_len - at(tail_head, __rust_mir_138_remaining))));
         solve() using { __rust_mir_155 == __rust_mir_138_base + (remainder_len - at(tail_head, __rust_mir_138_remaining)); __rust_mir_138_base + (remainder_len - at(tail_head, __rust_mir_138_remaining)) == bytes + ((bytes.len() - bytes.len() % 4u64) + (remainder_len - at(tail_head, __rust_mir_138_remaining))); };
        }
       step();
       step_until(assignment(__rust_mir_144, 0)); step();
       have to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64);
       have to_integer(((__rust_mir_138_remaining as u32) as i32)) == to_integer(at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1) by { rewrite(to_integer(__rust_mir_138_remaining), to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64)); solve(); }
       have __rust_mir_138_remaining <= bytes.len() by solve() using { to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64); 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have to_integer(1u64) <= to_integer(bytes.len() - __rust_mir_138_remaining) by solve() using { to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64); 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have 0 <= ((__rust_mir_138_remaining as u32) as i32) by solve() using { to_integer(((__rust_mir_138_remaining as u32) as i32)) == to_integer(at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1); 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); };
       have to_integer(bytes.len() - __rust_mir_138_remaining - 1u64) == to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining)) by solve() using { to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64); 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have __rust_mir_155 == bytes + (bytes.len() - __rust_mir_138_remaining - 1u64) by { rewrite(to_integer(bytes.len() - __rust_mir_138_remaining - 1u64), to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining))); known(); }
       have to_integer(bytes.len() - __rust_mir_138_remaining - 1u64) <= to_integer(18446744073709551614u64) by solve() using { to_integer(1u64) <= to_integer(bytes.len() - __rust_mir_138_remaining); __rust_mir_138_remaining <= bytes.len(); };
       have to_integer((bytes.len() - __rust_mir_138_remaining - 1u64)) <= to_integer(18446744073709551614u64);
       have to_integer(bytes.len() - __rust_mir_138_remaining - 1u64) + 1 <= 18446744073709551615 by solve() using { to_integer(bytes.len() - __rust_mir_138_remaining - 1u64) <= to_integer(18446744073709551614u64); };
       have to_integer((bytes.len() - __rust_mir_138_remaining - 1u64) + 1u64) == to_integer(bytes.len() - __rust_mir_138_remaining) by solve() using { to_integer(1u64) <= to_integer(bytes.len() - __rust_mir_138_remaining); __rust_mir_138_remaining <= bytes.len(); };
       have __rust_mir_144 == (__rust_mir_155[0] as u32);
       apply(adler_helper_byte_observation(__rust_mir_155[0])) using {};
       have to_integer(__rust_mir_144) == to_integer(((bytes + (bytes.len() - __rust_mir_138_remaining - 1u64))[0] as i32)) by { rewrite(__rust_mir_144, (__rust_mir_155[0] as u32)); rewrite(to_integer((__rust_mir_155[0] as u32)), to_integer((__rust_mir_155[0] as i32))); rewrite(__rust_mir_155, bytes + (bytes.len() - __rust_mir_138_remaining - 1u64)); normalize(); }
       have truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes, bytes.len() - __rust_mir_138_remaining - 1u64, old(to_integer((self.a as u32)))) by { rewrite(to_integer(bytes.len() - __rust_mir_138_remaining - 1u64), to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining))); solve(); }
       have truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes, bytes.len() - __rust_mir_138_remaining - 1u64, old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(bytes.len() - __rust_mir_138_remaining - 1u64), to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining))); solve(); }
       apply(adler_prefix_a_step_one_u64(bytes, bytes.len() - __rust_mir_138_remaining - 1u64, old(to_integer((self.a as u32))), to_integer(a))) using { to_integer(bytes.len() - __rust_mir_138_remaining - 1u64) + 1 <= 18446744073709551615; 0 <= old(to_integer((self.a as u32))); 0 <= to_integer(a); truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes, bytes.len() - __rust_mir_138_remaining - 1u64, old(to_integer((self.a as u32)))); };
       apply(adler_prefix_b_step_one_u64(bytes, bytes.len() - __rust_mir_138_remaining - 1u64, old(to_integer((self.a as u32))), old(to_integer((self.b as u32))), to_integer(a), to_integer(b))) using { to_integer(bytes.len() - __rust_mir_138_remaining - 1u64) + 1 <= 18446744073709551615; 0 <= old(to_integer((self.a as u32))); old(to_integer((self.a as u32))) <= 65520; 0 <= old(to_integer((self.b as u32))); 0 <= to_integer(a); 0 <= to_integer(b); truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes, bytes.len() - __rust_mir_138_remaining - 1u64, old(to_integer((self.a as u32)))); truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes, bytes.len() - __rust_mir_138_remaining - 1u64, old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); };
       have __rust_mir_144 <= 255u32;
       have to_integer(__rust_mir_144) <= to_integer(255u32);
       have to_integer(__rust_mir_144) <= 255 by solve() using { to_integer(__rust_mir_144) <= to_integer(255u32); };
       apply(adler_tail_iterator_step(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32)), to_integer(a), to_integer(b), to_integer(__rust_mir_144))) using { 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); ((remainder_len as u32) as i32) <= 3; to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32)))); to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32)))); to_integer(__rust_mir_144) <= 255; };
       have a <= 4294967295u32 - __rust_mir_144 by solve() using { to_integer(a) + to_integer(__rust_mir_144) <= 4294967295; };
       step_until(assignment(__rust_mir_146, 0));
       mark tail_add_a;
       have to_integer(at(tail_add_a, a)) == to_integer(a) by normalize();
       have to_integer(at(tail_add_a, b)) == to_integer(b) by normalize();
       have to_integer(at(tail_add_a, __rust_mir_144)) == to_integer(((bytes + (bytes.len() - __rust_mir_138_remaining - 1u64))[0] as i32)) by normalize() using { to_integer(__rust_mir_144) == to_integer(((bytes + (bytes.len() - __rust_mir_138_remaining - 1u64))[0] as i32)); };
       have truncating_remainder(to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)), 65521) == adler_spec_a_u64(bytes, bytes.len() - __rust_mir_138_remaining, old(to_integer((self.a as u32)))) by {
        rewrite(to_integer(bytes.len() - __rust_mir_138_remaining), to_integer((bytes.len() - __rust_mir_138_remaining - 1u64) + 1u64));
        rewrite(to_integer(at(tail_add_a, a)), to_integer(a));
        rewrite(to_integer(at(tail_add_a, __rust_mir_144)), to_integer(((bytes + (bytes.len() - __rust_mir_138_remaining - 1u64))[0] as i32)));
        known();
       }
       have truncating_remainder(to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)), 65521) == adler_spec_b_u64(bytes, bytes.len() - __rust_mir_138_remaining, old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by {
        rewrite(to_integer(bytes.len() - __rust_mir_138_remaining), to_integer((bytes.len() - __rust_mir_138_remaining - 1u64) + 1u64));
        rewrite(to_integer(at(tail_add_a, b)), to_integer(b));
        rewrite(to_integer(at(tail_add_a, a)), to_integer(a));
        rewrite(to_integer(at(tail_add_a, __rust_mir_144)), to_integer(((bytes + (bytes.len() - __rust_mir_138_remaining - 1u64))[0] as i32)));
        known();
       }

       have to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) <= 4294967295;
       step();
       have to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a) + at(tail_add_a, __rust_mir_144));
       have to_integer(at(tail_add_a, a) + at(tail_add_a, __rust_mir_144)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) by apply(integer::uint32_add_to_integer(at(tail_add_a, a), at(tail_add_a, __rust_mir_144))) using { to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) <= 4294967295; };
       have to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) by { rewrite(to_integer(__rust_mir_146), to_integer(at(tail_add_a, a) + at(tail_add_a, __rust_mir_144))); known(); }
       have to_integer(__rust_mir_146) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by solve() using { to_integer(a) + to_integer(__rust_mir_144) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); };
       have to_integer(b) + to_integer(__rust_mir_146) <= 4294967295 by solve() using { to_integer(b) + to_integer(a) + to_integer(__rust_mir_144) <= 4294967295; to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); };
       have to_integer(b) + to_integer(__rust_mir_146) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by solve() using { to_integer(b) + to_integer(a) + to_integer(__rust_mir_144) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); };
       step_until(assignment(a, 2)); step();
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1);
       have a == __rust_mir_146;
       have to_integer(a) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) by { rewrite(a, __rust_mir_146); known(); }
       have truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes, bytes.len() - __rust_mir_138_remaining, old(to_integer((self.a as u32)))) by { rewrite(to_integer(a), to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144))); known(); }
       step_until(assignment(__rust_mir_147, 0)); step();
       have __rust_mir_147 == a;
       have a == __rust_mir_146;
       have to_integer(b) + to_integer(__rust_mir_147) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by { rewrite(__rust_mir_147, a); rewrite(a, __rust_mir_146); known(); }
       have to_integer(b) + to_integer(__rust_mir_147) <= 4294967295;
       have b <= 4294967295u32 - __rust_mir_147 by solve() using { to_integer(b) + to_integer(__rust_mir_147) <= 4294967295; };
       step_until(assignment(__rust_mir_148, 0));
       mark tail_add_b;
       have to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b));
       have to_integer(at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144));

       have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by solve() using { to_integer(b) + to_integer(__rust_mir_147) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); };
       have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= 4294967295;
       step();
       have to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b) + at(tail_add_b, __rust_mir_147));
       have to_integer(at(tail_add_b, b) + at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) by apply(integer::uint32_add_to_integer(at(tail_add_b, b), at(tail_add_b, __rust_mir_147))) using { to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= 4294967295; };

       have to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) by { rewrite(to_integer(__rust_mir_148), to_integer(at(tail_add_b, b) + at(tail_add_b, __rust_mir_147))); known(); }
       have to_integer(__rust_mir_148) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by { rewrite(to_integer(__rust_mir_148), to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147))); known(); }
       step_until(assignment(b, 6)); step();
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1);
       have to_integer(b) == to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) by solve() using { to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)); to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b)); to_integer(at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); };
       have truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes, bytes.len() - __rust_mir_138_remaining, old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144))); known(); }
       step_until(back_edge());
        have to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64);
        have to_integer(((__rust_mir_138_remaining as u32) as i32)) == to_integer(at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1) by { rewrite(to_integer(__rust_mir_138_remaining), to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64)); solve(); }
       apply(adler_tail_remaining_progress(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32)))) using { 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((remainder_len as u32) as i32); ((remainder_len as u32) as i32) <= 3; };
       have adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)) == adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1 by { rewrite(to_integer(((__rust_mir_138_remaining as u32) as i32)), to_integer(at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1)); known(); }
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)), adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); known(); }
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)), adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); known(); }
       have 0 <= to_integer(a); have to_integer(a) <= 4294967295; have 0 <= to_integer(b); have to_integer(b) <= 4294967295; 
       have 0 <= ((__rust_mir_138_remaining as u32) as i32) and ((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32);
        have __rust_mir_138_remaining <= remainder_len by solve() using { to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64); 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; };
        have to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining)) <= to_integer(18446744073709551614u64) by solve() using { 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
        have to_integer(bytes.len() - __rust_mir_138_remaining) == to_integer((bytes.len() - at(tail_head, __rust_mir_138_remaining)) + 1u64) by solve() using { to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64); 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
        have __rust_mir_138_remaining < at(tail_head, __rust_mir_138_remaining) by solve() using { to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64); 1u64 <= at(tail_head, __rust_mir_138_remaining); };
      }
     }

     step_until(assignment(__rust_mir_149, 0));
     have at(loop(5).exit, __rust_mir_138_remaining) == 0u64 by solve() using { not (0u64 < at(loop(5).exit, __rust_mir_138_remaining)); };
     have truncating_remainder(to_integer(at(loop(5).exit, a)), 65521) == adler_spec_a_u64(bytes, bytes.len() - at(loop(5).exit, __rust_mir_138_remaining), old(to_integer((self.a as u32)))) by solve();
     have to_integer(a) == to_integer(at(loop(5).exit, a)) by normalize();
     have to_integer(bytes.len()) == to_integer(bytes.len() - at(loop(5).exit, __rust_mir_138_remaining)) by { rewrite(at(loop(5).exit, __rust_mir_138_remaining), 0u64); normalize(); }
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32)))) by { rewrite(to_integer(a), to_integer(at(loop(5).exit, a))); rewrite(to_integer(bytes.len()), to_integer(bytes.len() - at(loop(5).exit, __rust_mir_138_remaining))); known(); }
     have truncating_remainder(to_integer(at(loop(5).exit, b)), 65521) == adler_spec_b_u64(bytes, bytes.len() - at(loop(5).exit, __rust_mir_138_remaining), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by solve();
     have to_integer(b) == to_integer(at(loop(5).exit, b)) by normalize();
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), to_integer(at(loop(5).exit, b))); rewrite(to_integer(bytes.len()), to_integer(bytes.len() - at(loop(5).exit, __rust_mir_138_remaining))); known(); }
     have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) } by solve();
     apply(adler_spec_extensional_u64(bytes, old(bytes), bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) using { forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) }; };
     have adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32)))) == old(adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32))))) by normalize() using { adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32)))) == adler_spec_a_u64(old(bytes), bytes.len(), old(to_integer((self.a as u32)))); };
     have adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == old(adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by normalize() using { adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == adler_spec_b_u64(old(bytes), bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); };
     have truncating_remainder(to_integer(a), 65521) == old(adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32))))) by solve() using { truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32)))); adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32)))) == old(adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32))))); };
     have truncating_remainder(to_integer(b), 65521) == old(adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by solve() using { truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == old(adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };
     mark tail_done;
     have truncating_remainder(to_integer(at(tail_done, a)), 65521) == old(adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32))))) by normalize() using { truncating_remainder(to_integer(a), 65521) == old(adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32))))); };
     have truncating_remainder(to_integer(at(tail_done, b)), 65521) == old(adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by normalize() using { truncating_remainder(to_integer(b), 65521) == old(adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };

     have __rust_checked_34 == 65521u32;
     step();
     have __rust_mir_149 == __rust_checked_32 % __rust_checked_34 by solve() using {};
     have __rust_mir_149 == __rust_checked_32 % 65521u32 by { rewrite(__rust_mir_149, __rust_checked_32 % __rust_checked_34); rewrite(__rust_checked_34, 65521u32); normalize(); }
     have to_integer(__rust_checked_32) == to_integer(at(tail_done, a));
     apply(integer::uint32_remainder_to_integer(__rust_checked_32, 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(__rust_mir_149) == truncating_remainder(to_integer(__rust_checked_32), 65521) by { rewrite(__rust_mir_149, __rust_checked_32 % 65521u32); normalize() using { to_integer(__rust_checked_32 % 65521u32) == truncating_remainder(to_integer(__rust_checked_32), to_integer(65521u32)); }; }
     have to_integer(__rust_mir_149) == old(adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32))))) by { rewrite(to_integer(__rust_mir_149), truncating_remainder(to_integer(__rust_checked_32), 65521)); rewrite(to_integer(__rust_checked_32), to_integer(at(tail_done, a))); known(); }
     apply(integer::uint32_remainder_less_than_divisor(__rust_checked_32, 65521u32));
     have __rust_mir_149 < 65521u32 by { rewrite(__rust_mir_149, __rust_checked_32 % 65521u32); known(); }
     have 0 <= to_integer(__rust_mir_149);
     have to_integer(__rust_mir_149) <= 4294967295;
     have to_integer(__rust_mir_149) < 65521 by solve() using { to_integer(__rust_mir_149) < to_integer(65521u32); };
     have to_integer(__rust_mir_149) <= 65535 by solve() using { to_integer(__rust_mir_149) < 65521; };
     mark general_reduced_a;
     step_until(assignment(__rust_mir_151, 0));
     have __rust_checked_37 == 65521u32;
     step();
     have __rust_mir_151 == __rust_checked_35 % __rust_checked_37 by solve() using {};
     have __rust_mir_151 == __rust_checked_35 % 65521u32 by { rewrite(__rust_mir_151, __rust_checked_35 % __rust_checked_37); rewrite(__rust_checked_37, 65521u32); normalize(); }
     have to_integer(__rust_checked_35) == to_integer(at(tail_done, b));
     apply(integer::uint32_remainder_to_integer(__rust_checked_35, 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(__rust_mir_151) == truncating_remainder(to_integer(__rust_checked_35), 65521) by { rewrite(__rust_mir_151, __rust_checked_35 % 65521u32); normalize() using { to_integer(__rust_checked_35 % 65521u32) == truncating_remainder(to_integer(__rust_checked_35), to_integer(65521u32)); }; }
     have to_integer(__rust_mir_151) == old(adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by { rewrite(to_integer(__rust_mir_151), truncating_remainder(to_integer(__rust_checked_35), 65521)); rewrite(to_integer(__rust_checked_35), to_integer(at(tail_done, b))); solve(); }
     apply(integer::uint32_remainder_less_than_divisor(__rust_checked_35, 65521u32));
     have __rust_mir_151 < 65521u32 by { rewrite(__rust_mir_151, __rust_checked_35 % 65521u32); known(); }
     have 0 <= to_integer(__rust_mir_151);
     have to_integer(__rust_mir_151) <= 4294967295;
     have to_integer(__rust_mir_151) < to_integer(65521u32);
     have to_integer(__rust_mir_151) < 65521 by solve() using { to_integer(__rust_mir_151) < to_integer(65521u32); };
     have to_integer(__rust_mir_151) <= 65535 by solve() using { to_integer(__rust_mir_151) < 65521; };
     mark general_reduced_b;
     step_until(function.exit);
     have to_integer(self.a) == to_integer(at(general_reduced_a, __rust_mir_149)) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer(at(general_reduced_a, __rust_mir_149)) => 0 <= to_integer(at(general_reduced_a, __rust_mir_149));
     premise 1: to_integer(at(general_reduced_a, __rust_mir_149)) <= 65535 => to_integer(at(general_reduced_a, __rust_mir_149)) <= 65535;
     integer_cast_identity bounds [0, 1] => to_integer(self.a) == to_integer(at(general_reduced_a, __rust_mir_149)); conclusion 0;
     } }
     have to_integer(self.a) == old(adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32))))) by { rewrite(to_integer(self.a), to_integer(at(general_reduced_a, __rust_mir_149))); solve(); }
     have to_integer(at(general_reduced_a, __rust_mir_149)) < 65521;
     have to_integer(self.a) < 65521 by { rewrite(to_integer(self.a), to_integer(at(general_reduced_a, __rust_mir_149))); known(); }
     have to_integer(self.b) == to_integer(at(general_reduced_b, __rust_mir_151)) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer(at(general_reduced_b, __rust_mir_151)) => 0 <= to_integer(at(general_reduced_b, __rust_mir_151));
     premise 1: to_integer(at(general_reduced_b, __rust_mir_151)) <= 65535 => to_integer(at(general_reduced_b, __rust_mir_151)) <= 65535;
     integer_cast_identity bounds [0, 1] => to_integer(self.b) == to_integer(at(general_reduced_b, __rust_mir_151)); conclusion 0;
     } }
     have to_integer(self.b) == old(adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by { rewrite(to_integer(self.b), to_integer(at(general_reduced_b, __rust_mir_151))); solve(); }
     have to_integer(at(general_reduced_b, __rust_mir_151)) < 65521;
     have to_integer(self.b) < 65521 by { rewrite(to_integer(self.b), to_integer(at(general_reduced_b, __rust_mir_151))); known(); }
     have 0 <= to_integer(self.a) by { rewrite(to_integer(self.a), to_integer(at(general_reduced_a, __rust_mir_149))); solve() using { 0 <= to_integer(at(general_reduced_a, __rust_mir_149)); }; }
     have to_integer(self.a) <= 65535 by solve() using { to_integer(self.a) < 65521; };
     have to_integer((self.a as i32)) == to_integer(self.a) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer(self.a) => 0 <= to_integer(self.a);
     premise 1: to_integer(self.a) <= 65535 => to_integer(self.a) <= 65535;
     integer_cast_identity bounds [0, 1] => to_integer((self.a as i32)) == to_integer(self.a); conclusion 0;
     } }
     have to_integer((self.a as i32)) <= to_integer(65520) by { rewrite(to_integer((self.a as i32)), to_integer(self.a)); solve() using { to_integer(self.a) < 65521; }; }
     have ((self.a as i32)) <= 65520;
     apply(adler_i32_below_mod((self.a as i32))) using { (self.a as i32) <= 65520; };
     have self.a < 65521 by known();
     have 0 <= to_integer(self.b) by { rewrite(to_integer(self.b), to_integer(at(general_reduced_b, __rust_mir_151))); solve() using { 0 <= to_integer(at(general_reduced_b, __rust_mir_151)); }; }
     have to_integer(self.b) <= 65535 by solve() using { to_integer(self.b) < 65521; };
     have to_integer((self.b as i32)) == to_integer(self.b) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer(self.b) => 0 <= to_integer(self.b);
     premise 1: to_integer(self.b) <= 65535 => to_integer(self.b) <= 65535;
     integer_cast_identity bounds [0, 1] => to_integer((self.b as i32)) == to_integer(self.b); conclusion 0;
     } }
     have to_integer((self.b as i32)) <= to_integer(65520) by { rewrite(to_integer((self.b as i32)), to_integer(self.b)); solve() using { to_integer(self.b) < 65521; }; }
     have ((self.b as i32)) <= 65520;
     apply(adler_i32_below_mod((self.b as i32))) using { (self.b as i32) <= 65520; };
     have self.b < 65521 by known();
     have to_integer(self.a) <= 65520 by solve() using { to_integer(self.a) < 65521; };
     have to_integer(self.b) <= 65520 by solve() using { to_integer(self.b) < 65521; };
     solve() using { self.a < 65521; self.b < 65521; to_integer(self.a) <= 65520; to_integer(self.b) <= 65520; to_integer(self.a) == old(adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32))))); to_integer(self.b) == old(adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };
    }
}
