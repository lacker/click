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

theorem adler_uint64_self_subtract(n: uint64) { ensures to_integer(n - n) == to_integer(0u64) by close(); }
theorem adler_i32_below_mod(n: int32) { requires n <= 65520; ensures n < 65521 by close() using { n <= 65520; }; }
theorem adler_bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22204;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by close() using { 0 <= index; index <= 22204; };
  apply(integer::uint8_pointer_add_associate_int32(base, index, 4));
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
  close() using { 0 <= to_integer(length); to_integer(length) <= 22204; 0 <= to_integer(seed); to_integer(seed) <= 65520; };
 }
}
theorem adler_small_length_cast(length: uint64) {
 requires length <= 22204u64;
 ensures (length as u32) <= 22204u32 by {
  have 0u64 <= length by close();
  have 0 <= to_integer(length) by close();
  have to_integer(length) <= 4294967295 by close() using { to_integer(length) <= 22204; };
  have to_integer((length as u32)) == to_integer(length) by {
   close() using { 0 <= to_integer(length); to_integer(length) <= 4294967295; };
  }
  have to_integer((length as u32)) <= to_integer(22204u32) by { rewrite(to_integer((length as u32)), to_integer(length)); close(); }
  close();
 }
}



theorem adler_tail_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 2147483646;
 ensures (base + index) + 1 == base + (index + 1) by {
  have defined(index + 1) by close() using { 0 <= index; index <= 2147483646; };
  apply(integer::uint8_pointer_add_associate_int32(base, index, 1));
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
  apply(adler_spec_a_canonical_u64(bytes, n, a_seed));
  apply(adler_spec_empty(bytes + n, adler_spec_a_u64(bytes, n, a_seed), 0));
  have truncating_remainder(adler_lane_a(a, to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)) by {
   rewrite(adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)), adler_spec_a_u64(bytes, n, a_seed));
   close();
  }
  have to_integer(v1) == to_integer((bytes + n)[0 + 1] as int32) by close() using { to_integer(v1) == to_integer((bytes + n)[1] as int32); };
  have to_integer(v2) == to_integer((bytes + n)[0 + 2] as int32) by close() using { to_integer(v2) == to_integer((bytes + n)[2] as int32); };
  have to_integer(v3) == to_integer((bytes + n)[0 + 3] as int32) by close() using { to_integer(v3) == to_integer((bytes + n)[3] as int32); };
  apply(adler_native_four_lane_a_prefix_step(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), a, a0, a1, a2, a3, v0, v1, v2, v3));
  have to_integer(0 + 4) == to_integer(4u64) by close();
  apply(adler_spec_a_bridge(bytes + n, 0 + 4, 4u64, adler_spec_a_u64(bytes, n, a_seed)));
  have to_integer(n) + to_integer(4u64) <= 18446744073709551615 by close() using { to_integer(n) + 4 <= 18446744073709551615; };
  apply(adler_spec_a_concat_u64(bytes, n, 4u64, a_seed));
  close() using {
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
  apply(adler_spec_a_canonical_u64(bytes, n, a_seed));
  apply(adler_spec_b_canonical_u64(bytes, n, a_seed, b_seed));
  apply(adler_spec_empty(bytes + n, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)));
  have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)) by {
   rewrite(adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)), adler_spec_a_u64(bytes, n, a_seed));
   close();
  }
  have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)), 65521) == adler_spec_b(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)) by {
   rewrite(adler_spec_b(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)), adler_spec_b_u64(bytes, n, a_seed, b_seed));
   close();
  }
  have to_integer(v1) == to_integer((bytes + n)[0 + 1] as int32) by close() using { to_integer(v1) == to_integer((bytes + n)[1] as int32); };
  have to_integer(v2) == to_integer((bytes + n)[0 + 2] as int32) by close() using { to_integer(v2) == to_integer((bytes + n)[2] as int32); };
  have to_integer(v3) == to_integer((bytes + n)[0 + 3] as int32) by close() using { to_integer(v3) == to_integer((bytes + n)[3] as int32); };
  apply(adler_native_deferred_b_prefix_step(bytes + n, 0, pos, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed), a, b, a0, a1, a2, a3, b0, b1, b2, b3, v0, v1, v2, v3));
  have to_integer(0 + 4) == to_integer(4u64) by close();
  apply(adler_spec_b_bridge(bytes + n, 0 + 4, 4u64, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)));
  have to_integer(n) + to_integer(4u64) <= 18446744073709551615 by close() using { to_integer(n) + 4 <= 18446744073709551615; };
  apply(adler_spec_b_concat_u64(bytes, n, 4u64, a_seed, b_seed));
  close() using {
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
  apply(adler_spec_a_canonical_u64(bytes, n, seed));
  apply(adler_spec_empty(bytes + n, adler_spec_a_u64(bytes, n, seed), 0));
  have truncating_remainder(representative, 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, seed)) by {
   rewrite(adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, seed)), adler_spec_a_u64(bytes, n, seed));
   close();
  }
  apply(adler_prefix_a_step_one(bytes + n, 0, adler_spec_a_u64(bytes, n, seed), representative));
  have to_integer(0 + 1) == to_integer(1u64) by close();
  apply(adler_spec_a_bridge(bytes + n, 0 + 1, 1u64, adler_spec_a_u64(bytes, n, seed)));
  have to_integer(n) + to_integer(1u64) <= 18446744073709551615 by close() using { to_integer(n) + 1 <= 18446744073709551615; };
  apply(adler_spec_a_concat_u64(bytes, n, 1u64, seed));
  rewrite(
   truncating_remainder(representative + to_integer((bytes + n)[0] as int32), 65521),
   adler_spec_a(bytes + n, 0 + 1, adler_spec_a_u64(bytes, n, seed))
  );
  rewrite(
   adler_spec_a(bytes + n, 0 + 1, adler_spec_a_u64(bytes, n, seed)),
   adler_spec_a_u64(bytes + n, 1u64, adler_spec_a_u64(bytes, n, seed))
  );
  rewrite(
   adler_spec_a_u64(bytes, n + 1u64, seed),
   adler_spec_a_u64(bytes + n, 1u64, adler_spec_a_u64(bytes, n, seed))
  );
  close();
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
  apply(adler_spec_a_canonical_u64(bytes, n, a_seed));
  apply(adler_spec_b_canonical_u64(bytes, n, a_seed, b_seed));
  apply(adler_spec_empty(bytes + n, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)));
  have truncating_remainder(a_rep, 65521) == adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)) by {
   rewrite(adler_spec_a(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed)), adler_spec_a_u64(bytes, n, a_seed));
   close();
  }
  have truncating_remainder(b_rep, 65521) == adler_spec_b(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)) by {
   rewrite(adler_spec_b(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)), adler_spec_b_u64(bytes, n, a_seed, b_seed));
   close();
  }
  apply(adler_prefix_b_step_one(bytes + n, 0, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed), a_rep, b_rep));
  have to_integer(0 + 1) == to_integer(1u64) by close();
  apply(adler_spec_b_bridge(bytes + n, 0 + 1, 1u64, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)));
  have to_integer(n) + to_integer(1u64) <= 18446744073709551615 by close() using { to_integer(n) + 1 <= 18446744073709551615; };
  apply(adler_spec_b_concat_u64(bytes, n, 1u64, a_seed, b_seed));
  rewrite(
   truncating_remainder((b_rep + a_rep + to_integer((bytes + n)[0] as int32)), 65521),
   adler_spec_b(bytes + n, 0 + 1, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed))
  );
  rewrite(
   adler_spec_b(bytes + n, 0 + 1, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed)),
   adler_spec_b_u64(bytes + n, 1u64, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed))
  );
  rewrite(
   adler_spec_b_u64(bytes, n + 1u64, a_seed, b_seed),
   adler_spec_b_u64(bytes + n, 1u64, adler_spec_a_u64(bytes, n, a_seed), adler_spec_b_u64(bytes, n, a_seed, b_seed))
  );
  close();
 }
}

// The byte count the chunks an iterator still holds stand for. The library model gives
// the iterator only as `len()` chunks; the proofs below keep counting remaining bytes.

function adler_chunk_bytes(count: uint64, size: uint64) -> uint64 { count * size }

theorem adler_chunk_bytes_none(size: uint64) {
 ensures adler_chunk_bytes(0u64, size) == 0u64 by { unfold(adler_chunk_bytes(0u64, size)); close(); }
}
theorem adler_chunk_bytes_exact_4(count: uint64, n: uint64) {
 requires count <= n / 4u64;
 ensures to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4 by {
  have n / 4u64 <= 4611686018427387903u64;
  have count <= 4611686018427387903u64;
  have to_integer(count * 4u64) == to_integer(count) * 4;
  unfold(adler_chunk_bytes(count, 4u64));
  close();
 }
}
theorem adler_chunk_bytes_exact_22208(count: uint64, n: uint64) {
 requires count <= n / 22208u64;
 ensures to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208 by {
  have n / 22208u64 <= 830635089774385u64;
  have count <= 830635089774385u64;
  have to_integer(count * 22208u64) == to_integer(count) * 22208;
  unfold(adler_chunk_bytes(count, 22208u64));
  close();
 }
}
theorem adler_quotient_4(n: uint64) {
 ensures to_integer(n / 4u64) * 4 == to_integer(n - n % 4u64) by {
  apply(integer::truncation_identity(to_integer(n), 4));
  have to_integer(4u64) != 0 by { close(); }
  apply(integer::uint64_remainder_to_integer(n, 4u64));
  apply(integer::uint64_divide_to_integer(n, 4u64));
  have n % 4u64 <= n by close();
  have to_integer(n - (n % 4u64)) == to_integer(n) - to_integer((n % 4u64));
  rewrite(to_integer(n - n % 4u64), to_integer(n) - to_integer(n % 4u64));
  rewrite(to_integer(n % 4u64), truncating_remainder(to_integer(n), to_integer(4u64)));
  rewrite(to_integer(n / 4u64), truncating_quotient(to_integer(n), to_integer(4u64)));
  close() using { to_integer(n) == truncating_quotient(to_integer(n), 4) * 4 + truncating_remainder(to_integer(n), 4); };
 }
}
theorem adler_quotient_22208(n: uint64) {
 ensures to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64) by {
  apply(integer::truncation_identity(to_integer(n), 22208));
  have to_integer(22208u64) != 0 by { close(); }
  apply(integer::uint64_remainder_to_integer(n, 22208u64));
  apply(integer::uint64_divide_to_integer(n, 22208u64));
  have n % 22208u64 <= n by close();
  have to_integer(n - (n % 22208u64)) == to_integer(n) - to_integer((n % 22208u64));
  rewrite(to_integer(n - n % 22208u64), to_integer(n) - to_integer(n % 22208u64));
  rewrite(to_integer(n % 22208u64), truncating_remainder(to_integer(n), to_integer(22208u64)));
  rewrite(to_integer(n / 22208u64), truncating_quotient(to_integer(n), to_integer(22208u64)));
  close() using { to_integer(n) == truncating_quotient(to_integer(n), 22208) * 22208 + truncating_remainder(to_integer(n), 22208); };
 }
}
theorem adler_full_chunk_quotient(n: uint64) {
 ensures (n - n % 22208u64) / 22208u64 == n / 22208u64 by {
  apply(adler_quotient_22208(n));
  have to_integer(n - n % 22208u64) == to_integer(n / 22208u64) * 22208 + 0 by {
   rewrite(to_integer(n - n % 22208u64), to_integer(n / 22208u64) * 22208);
   close();
  }
  apply(integer::nonnegative_quotient_from_remainder(to_integer(n - n % 22208u64), 22208, to_integer(n / 22208u64), 0));
  apply(integer::uint64_divide_to_integer(n - n % 22208u64, 22208u64));
  rewrite(to_integer((n - n % 22208u64) / 22208u64), truncating_quotient(to_integer(n - n % 22208u64), 22208));
  close();
 }
}

theorem adler_chunk_bytes_full_4(n: uint64) {
 ensures to_integer(adler_chunk_bytes(n / 4u64, 4u64)) == to_integer(n - n % 4u64) by {
  have n / 4u64 <= n / 4u64 by close();
  apply(adler_chunk_bytes_exact_4(n / 4u64, n));
  apply(adler_quotient_4(n));
  close() using { to_integer(adler_chunk_bytes(n / 4u64, 4u64)) == to_integer(n / 4u64) * 4; to_integer(n / 4u64) * 4 == to_integer(n - n % 4u64); };
 }
}
theorem adler_chunk_bytes_whole_4(n: uint64) {
 requires n % 4u64 == 0u64;
 ensures adler_chunk_bytes(n / 4u64, 4u64) == n by {
  apply(adler_chunk_bytes_full_4(n));
  have to_integer(n - n % 4u64) == to_integer(n) by { rewrite(n % 4u64, 0u64); close(); }
  have to_integer(adler_chunk_bytes(n / 4u64, 4u64)) == to_integer(n) by close() using { to_integer(adler_chunk_bytes(n / 4u64, 4u64)) == to_integer(n - n % 4u64); to_integer(n - n % 4u64) == to_integer(n); };
  close();
 }
}
theorem adler_chunk_bytes_next_4(count: uint64, n: uint64) {
 requires 0u64 < count;
 requires count <= n / 4u64;
 ensures 4u64 <= adler_chunk_bytes(count, 4u64) by {
  apply(adler_chunk_bytes_exact_4(count, n));
  close() using { to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; 0u64 < count; };
 }
 ensures to_integer(adler_chunk_bytes(count - 1u64, 4u64)) == to_integer(adler_chunk_bytes(count, 4u64) - 4u64) by {
  apply(adler_chunk_bytes_exact_4(count, n));
  have to_integer(count - 1u64) == to_integer(count) - 1 by close() using { 0u64 < count; };
  have to_integer(count - 1u64) <= to_integer(n / 4u64) by close() using { to_integer(count - 1u64) == to_integer(count) - 1; count <= n / 4u64; };
  apply(adler_chunk_bytes_exact_4(count - 1u64, n));
  have 4u64 <= adler_chunk_bytes(count, 4u64) by close() using { to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; 0u64 < count; };
  have to_integer(adler_chunk_bytes(count, 4u64) - 4u64) == to_integer(adler_chunk_bytes(count, 4u64)) - 4 by close() using { 4u64 <= adler_chunk_bytes(count, 4u64); };
  close() using { to_integer(adler_chunk_bytes(count - 1u64, 4u64)) == to_integer(count - 1u64) * 4; to_integer(count - 1u64) == to_integer(count) - 1; to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; to_integer(adler_chunk_bytes(count, 4u64) - 4u64) == to_integer(adler_chunk_bytes(count, 4u64)) - 4; };
 }
}
theorem adler_chunk_bytes_offset_4(count: uint64, n: uint64) {
 requires count <= n / 4u64;
 ensures to_integer(adler_chunk_bytes(count, 4u64)) <= to_integer(n - n % 4u64) by {
  apply(adler_chunk_bytes_exact_4(count, n));
  apply(adler_quotient_4(n));
  close() using { to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; to_integer(n / 4u64) * 4 == to_integer(n - n % 4u64); count <= n / 4u64; };
 }
 ensures to_integer((n / 4u64 - count) * 4u64) == to_integer((n - n % 4u64) - adler_chunk_bytes(count, 4u64)) by {
  apply(adler_chunk_bytes_exact_4(count, n));
  apply(adler_quotient_4(n));
  have to_integer(n / 4u64 - count) == to_integer(n / 4u64) - to_integer(count) by close() using { count <= n / 4u64; };
  have n / 4u64 <= 4611686018427387903u64;
  have n / 4u64 - count <= 4611686018427387903u64 by close() using { n / 4u64 <= 4611686018427387903u64; count <= n / 4u64; to_integer(n / 4u64 - count) == to_integer(n / 4u64) - to_integer(count); };
  have to_integer((n / 4u64 - count) * 4u64) == to_integer(n / 4u64 - count) * 4;
  have to_integer(adler_chunk_bytes(count, 4u64)) <= to_integer(n - n % 4u64) by close() using { to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; to_integer(n / 4u64) * 4 == to_integer(n - n % 4u64); count <= n / 4u64; };
  apply(integer::uint64_subtract_to_integer(n - n % 4u64, adler_chunk_bytes(count, 4u64)));
  close() using { to_integer((n / 4u64 - count) * 4u64) == to_integer(n / 4u64 - count) * 4; to_integer(n / 4u64 - count) == to_integer(n / 4u64) - to_integer(count); to_integer(adler_chunk_bytes(count, 4u64)) == to_integer(count) * 4; to_integer(n / 4u64) * 4 == to_integer(n - n % 4u64); to_integer((n - n % 4u64) - adler_chunk_bytes(count, 4u64)) == to_integer(n - n % 4u64) - to_integer(adler_chunk_bytes(count, 4u64)); };
 }
}
theorem adler_chunk_bytes_offset_whole_4(count: uint64, n: uint64) {
 requires count <= n / 4u64;
 requires n % 4u64 == 0u64;
 ensures adler_chunk_bytes(count, 4u64) <= n by {
  apply(adler_chunk_bytes_offset_4(count, n));
  have to_integer(n - n % 4u64) == to_integer(n) by { rewrite(n % 4u64, 0u64); close(); }
  close() using { to_integer(adler_chunk_bytes(count, 4u64)) <= to_integer(n - n % 4u64); to_integer(n - n % 4u64) == to_integer(n); };
 }
 ensures to_integer((n / 4u64 - count) * 4u64) == to_integer(n - adler_chunk_bytes(count, 4u64)) by {
  apply(adler_chunk_bytes_offset_4(count, n));
  rewrite(to_integer((n / 4u64 - count) * 4u64), to_integer((n - n % 4u64) - adler_chunk_bytes(count, 4u64)));
  rewrite(n % 4u64, 0u64);
  close();
 }
}
theorem adler_chunk_bytes_full_22208(n: uint64) {
 ensures to_integer(adler_chunk_bytes(n / 22208u64, 22208u64)) == to_integer(n - n % 22208u64) by {
  have n / 22208u64 <= n / 22208u64 by close();
  apply(adler_chunk_bytes_exact_22208(n / 22208u64, n));
  apply(adler_quotient_22208(n));
  close() using { to_integer(adler_chunk_bytes(n / 22208u64, 22208u64)) == to_integer(n / 22208u64) * 22208; to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64); };
 }
 ensures to_integer(adler_chunk_bytes(n / 22208u64, 22208u64)) == to_integer(n) - to_integer(n % 22208u64) by {
  have n % 22208u64 <= n by close();
  apply(integer::uint64_subtract_to_integer(n, n % 22208u64));
  apply(adler_chunk_bytes_exact_22208(n / 22208u64, n));
  apply(adler_quotient_22208(n));
  close() using {
   to_integer(adler_chunk_bytes(n / 22208u64, 22208u64)) == to_integer(n / 22208u64) * 22208;
   to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64);
   to_integer(n - n % 22208u64) == to_integer(n) - to_integer(n % 22208u64);
  };
 }
 ensures to_integer(n) - to_integer(n % 22208u64) <= to_integer(n) by {
  have 0 <= to_integer(n % 22208u64) by close();
  apply(integer::subtract_left_order(0, to_integer(n % 22208u64), to_integer(n)));
  close() using { to_integer(n) - to_integer(n % 22208u64) <= to_integer(n) - 0; };
 }
}
theorem adler_chunk_bytes_whole_22208(n: uint64) {
 requires n % 22208u64 == 0u64;
 ensures adler_chunk_bytes(n / 22208u64, 22208u64) == n by {
  apply(adler_chunk_bytes_full_22208(n));
  have to_integer(n - n % 22208u64) == to_integer(n) by { rewrite(n % 22208u64, 0u64); close(); }
  have to_integer(adler_chunk_bytes(n / 22208u64, 22208u64)) == to_integer(n) by close() using { to_integer(adler_chunk_bytes(n / 22208u64, 22208u64)) == to_integer(n - n % 22208u64); to_integer(n - n % 22208u64) == to_integer(n); };
  close();
 }
}
theorem adler_chunk_bytes_next_22208(count: uint64, n: uint64) {
 requires 0u64 < count;
 requires count <= n / 22208u64;
 ensures 22208u64 <= adler_chunk_bytes(count, 22208u64) by {
  apply(adler_chunk_bytes_exact_22208(count, n));
  close() using { to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; 0u64 < count; };
 }
 ensures to_integer(adler_chunk_bytes(count - 1u64, 22208u64)) == to_integer(adler_chunk_bytes(count, 22208u64) - 22208u64) by {
  apply(adler_chunk_bytes_exact_22208(count, n));
  have to_integer(count - 1u64) == to_integer(count) - 1 by close() using { 0u64 < count; };
  have to_integer(count - 1u64) <= to_integer(n / 22208u64) by close() using { to_integer(count - 1u64) == to_integer(count) - 1; count <= n / 22208u64; };
  apply(adler_chunk_bytes_exact_22208(count - 1u64, n));
  have 22208u64 <= adler_chunk_bytes(count, 22208u64) by close() using { to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; 0u64 < count; };
  have to_integer(adler_chunk_bytes(count, 22208u64) - 22208u64) == to_integer(adler_chunk_bytes(count, 22208u64)) - 22208 by close() using { 22208u64 <= adler_chunk_bytes(count, 22208u64); };
  close() using { to_integer(adler_chunk_bytes(count - 1u64, 22208u64)) == to_integer(count - 1u64) * 22208; to_integer(count - 1u64) == to_integer(count) - 1; to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; to_integer(adler_chunk_bytes(count, 22208u64) - 22208u64) == to_integer(adler_chunk_bytes(count, 22208u64)) - 22208; };
 }
}
theorem adler_chunk_bytes_offset_22208(count: uint64, n: uint64) {
 requires count <= n / 22208u64;
 ensures to_integer(adler_chunk_bytes(count, 22208u64)) <= to_integer(n - n % 22208u64) by {
  apply(adler_chunk_bytes_exact_22208(count, n));
  apply(adler_quotient_22208(n));
  close() using { to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64); count <= n / 22208u64; };
 }
 ensures to_integer((n / 22208u64 - count) * 22208u64) == to_integer((n - n % 22208u64) - adler_chunk_bytes(count, 22208u64)) by {
  apply(adler_chunk_bytes_exact_22208(count, n));
  apply(adler_quotient_22208(n));
  have to_integer(n / 22208u64 - count) == to_integer(n / 22208u64) - to_integer(count) by close() using { count <= n / 22208u64; };
  have n / 22208u64 <= 830635089774385u64;
  have n / 22208u64 - count <= 830635089774385u64 by close() using { n / 22208u64 <= 830635089774385u64; count <= n / 22208u64; to_integer(n / 22208u64 - count) == to_integer(n / 22208u64) - to_integer(count); };
  have to_integer((n / 22208u64 - count) * 22208u64) == to_integer(n / 22208u64 - count) * 22208;
  have to_integer(adler_chunk_bytes(count, 22208u64)) <= to_integer(n - n % 22208u64) by close() using { to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64); count <= n / 22208u64; };
  apply(integer::uint64_subtract_to_integer(n - n % 22208u64, adler_chunk_bytes(count, 22208u64)));
  close() using { to_integer((n / 22208u64 - count) * 22208u64) == to_integer(n / 22208u64 - count) * 22208; to_integer(n / 22208u64 - count) == to_integer(n / 22208u64) - to_integer(count); to_integer(adler_chunk_bytes(count, 22208u64)) == to_integer(count) * 22208; to_integer(n / 22208u64) * 22208 == to_integer(n - n % 22208u64); to_integer((n - n % 22208u64) - adler_chunk_bytes(count, 22208u64)) == to_integer(n - n % 22208u64) - to_integer(adler_chunk_bytes(count, 22208u64)); };
 }
}
theorem adler_chunk_bytes_offset_whole_22208(count: uint64, n: uint64) {
 requires count <= n / 22208u64;
 requires n % 22208u64 == 0u64;
 ensures adler_chunk_bytes(count, 22208u64) <= n by {
  apply(adler_chunk_bytes_offset_22208(count, n));
  have to_integer(n - n % 22208u64) == to_integer(n) by { rewrite(n % 22208u64, 0u64); close(); }
  close() using { to_integer(adler_chunk_bytes(count, 22208u64)) <= to_integer(n - n % 22208u64); to_integer(n - n % 22208u64) == to_integer(n); };
 }
 ensures to_integer((n / 22208u64 - count) * 22208u64) == to_integer(n - adler_chunk_bytes(count, 22208u64)) by {
  apply(adler_chunk_bytes_offset_22208(count, n));
  rewrite(to_integer((n / 22208u64 - count) * 22208u64), to_integer((n - n % 22208u64) - adler_chunk_bytes(count, 22208u64)));
  rewrite(n % 22208u64, 0u64);
  close();
 }
}

theorem adler_uint64_pointer_association(base: const uint8*, p: uint64, q: uint64) {
 requires to_integer(p) + to_integer(q) <= 18446744073709551615;
 ensures (base + p) + q == base + (p + q) by {
  apply(integer::uint64_add_to_integer(p, q));
  close() using { to_integer(p + q) == to_integer(p) + to_integer(q); };
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
  close() using { to_integer(p + ((n - p) - r)) == to_integer(n - r); };
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
  close();
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
     ensures to_integer(self.a) == old(adler_spec_a_u64(bytes.as_ptr(), bytes.len(), old(to_integer((self.a as u32)))));
     ensures to_integer(self.b) == old(adler_spec_b_u64(bytes.as_ptr(), bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
    } by {
     apply(adler_general_prefix_divisible_u64(bytes.len()));
     apply(adler_outer_bulk_divisible_u64(bytes.len() - bytes.len() % 4u64));
     apply(adler_general_tail_metadata_u64(bytes.len()));
     apply(adler_full_chunk_quotient(bytes.len() - bytes.len() % 4u64));
     apply(adler_chunk_bytes_full_22208(bytes.len() - bytes.len() % 4u64));
     have bytes.len() % 4u64 <= bytes.len() by close();
     step_until(assignment(b, 0).entry); step();
     have a <= 65520u32;
     have b <= 65520u32;
     step_until(loop(0).entry);
     // The outer iterator starts at the prefix the split retained.
     have bytes.as_ptr() == old(bytes.as_ptr()) by close();
     have bytes.len() == old(bytes.len() - bytes.len() % 4u64) by close();
     have remainder.len() == old(bytes.len() % 4u64) by close() using {
      old(to_integer(bytes.len() - (bytes.len() - bytes.len() % 4u64))) == old(to_integer(bytes.len() % 4u64));
     };
     have loop(0).iter.chunk_size == 22208u64 by close();
     have loop(0).iter.v == bytes.as_ptr() by close();
     have bytes.len() % 22208u64 <= bytes.len() by close();
     have loop(0).iter.v.len() == bytes.len() - bytes.len() % 22208u64 by {
      rewrite(loop(0).iter.chunk_size, 22208u64);
      close();
     }
     have remainder_chunk.len() == bytes.len() % 22208u64 by {
      rewrite(loop(0).iter.chunk_size, 22208u64);
      close();
     }
     have remainder_chunk.as_ptr() == bytes.as_ptr() + loop(0).iter.v.len() by close();
     have to_integer(a_vec.0[0]) <= 65520;
     have to_integer(a_vec.0[1]) <= 65520;
     have to_integer(a_vec.0[2]) <= 65520;
     have to_integer(a_vec.0[3]) <= 65520;
     have to_integer(b_vec.0[0]) <= 65520;
     have to_integer(b_vec.0[1]) <= 65520;
     have to_integer(b_vec.0[2]) <= 65520;
     have to_integer(b_vec.0[3]) <= 65520;
     have bytes.len() % 4u64 == 0u64 by {
      rewrite(bytes.len(), old(bytes.len() - bytes.len() % 4u64));
      close();
     }
     have loop(0).iter.len() == bytes.len() / 22208u64 by {
      rewrite(loop(0).iter.chunk_size, 22208u64);
      close() using {
       old(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) / 22208u64) == old((bytes.len() - bytes.len() % 4u64) / 22208u64);
      };
     }
     have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(loop(0).iter.v.len()) by {
      rewrite(loop(0).iter.len(), bytes.len() / 22208u64);
      rewrite(loop(0).iter.v.len(), bytes.len() - bytes.len() % 22208u64);
      close() using {
       old(to_integer(adler_chunk_bytes((bytes.len() - bytes.len() % 4u64) / 22208u64, 22208u64))) ==
        old(to_integer(bytes.len() - bytes.len() % 4u64) - to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64));
      };
     }
     have to_integer(bytes.len() % 22208u64) <= to_integer(bytes.len()) by close();
     have to_integer(loop(0).iter.v.len()) <= to_integer(bytes.len()) by {
      rewrite(loop(0).iter.v.len(), bytes.len() - bytes.len() % 22208u64);
      close() using {
       old(to_integer(bytes.len() - bytes.len() % 4u64) - to_integer((bytes.len() - bytes.len() % 4u64) % 22208u64)) <=
        old(to_integer(bytes.len() - bytes.len() % 4u64));
      };
     }
     have to_integer((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == 0 by {
      rewrite(to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(loop(0).iter.v.len()));
      rewrite(loop(0).iter.v.len(), bytes.len() - bytes.len() % 22208u64);
      close();
     }
     // Establish the empty original-input prefix before the full-batch loop.
     apply(adler_spec_empty_u64(bytes.as_ptr(), to_integer(a), 0));
     have to_integer(a_vec.0[0]) == 0;
     have to_integer(a_vec.0[1]) == 0;
     have to_integer(a_vec.0[2]) == 0;
     have to_integer(a_vec.0[3]) == 0;
     have adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) == to_integer(a) by { unfold(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); close() using { to_integer(a_vec.0[0]) == 0; to_integer(a_vec.0[1]) == 0; to_integer(a_vec.0[2]) == 0; to_integer(a_vec.0[3]) == 0; }; }
     have to_integer(a) == 0 * 65521 + to_integer(a) by close() using {};
     apply(adler_residue_unique(to_integer(a), 0, to_integer(a)));
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a)) by { rewrite(to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(0u64)); rewrite(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), to_integer(a)); unfold(adler_spec_a_u64(bytes.as_ptr(), 0u64, to_integer(a))); apply(adler_sum_empty_u64(bytes.as_ptr(), 0)); rewrite(adler_byte_sum_u64(bytes.as_ptr(), 0u64), 0); close(); }
     // Keep the entry B seed fixed while the working scalar B is reduced.
     have to_integer(b) == old(to_integer((self.b as u32))) by close();
     have 0 <= old(to_integer((self.b as u32))) by close() using { 0 <= to_integer(b); to_integer(b) == old(to_integer((self.b as u32))); };
     have old(to_integer((self.b as u32))) <= 65520 by close() using { to_integer(b) <= 65520; to_integer(b) == old(to_integer((self.b as u32))); };
     apply(adler_spec_empty_u64(bytes.as_ptr(), to_integer(a), old(to_integer((self.b as u32)))));
     have to_integer(b_vec.0[0]) == 0;
     have to_integer(b_vec.0[1]) == 0;
     have to_integer(b_vec.0[2]) == 0;
     have to_integer(b_vec.0[3]) == 0;
     apply(adler_zero_lane_b_residue(to_integer(b)));
     have adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) == adler_lane_b(to_integer(b), 0, 0, 0, 0, 0, 0, 0) by {
      rewrite(to_integer(a_vec.0[1]), 0);
      rewrite(to_integer(a_vec.0[2]), 0);
      rewrite(to_integer(a_vec.0[3]), 0);
      rewrite(to_integer(b_vec.0[0]), 0);
      rewrite(to_integer(b_vec.0[1]), 0);
      rewrite(to_integer(b_vec.0[2]), 0);
      rewrite(to_integer(b_vec.0[3]), 0);
      close();
     }
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(0u64)); rewrite(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), adler_lane_b(to_integer(b), 0, 0, 0, 0, 0, 0, 0)); close() using { truncating_remainder(adler_lane_b(to_integer(b), 0, 0, 0, 0, 0, 0, 0), 65521) == to_integer(b); adler_spec_b_u64(bytes.as_ptr(), 0u64, to_integer(a), old(to_integer((self.b as u32)))) == old(to_integer((self.b as u32))); to_integer(b) == old(to_integer((self.b as u32))); }; }
     have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) } by close();
     have loop(0).iter.len() <= (bytes.len()) / 22208u64;
     loop {
     decreases loop(0).iter.len();
     invariant loop(0).iter.chunk_size == 22208u64;
     invariant loop(0).iter.v.len() == adler_chunk_bytes(loop(0).iter.len(), 22208u64);
     invariant to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len());
     invariant to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
     owns a_vec.0[0..4]; owns b_vec.0[0..4];
     views *bytes;
     invariant bytes.as_ptr() == old(bytes.as_ptr());
     invariant forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
     invariant bytes.len() == old(bytes.len() - bytes.len() % 4u64);
     invariant a <= 65520u32;
     invariant b <= 65520u32;
     invariant adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
     invariant remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
     invariant remainder_chunk.len() == (bytes.len()) % 22208u64;
     invariant remainder.len() == old(bytes.len() % 4u64);
     invariant to_integer(a_vec.0[0]) <= 65520;
     invariant to_integer(a_vec.0[1]) <= 65520;
     invariant to_integer(a_vec.0[2]) <= 65520;
     invariant to_integer(a_vec.0[3]) <= 65520;
     invariant to_integer(b_vec.0[0]) <= 65520;
     invariant to_integer(b_vec.0[1]) <= 65520;
     invariant to_integer(b_vec.0[2]) <= 65520;
     invariant to_integer(b_vec.0[3]) <= 65520;
     invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a));
     invariant 0 <= old(to_integer((self.b as u32)));
     invariant truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32))));
     invariant loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
     invariant to_integer(loop(0).iter.len()) + iterations == to_integer((bytes.len()) / 22208u64);

     initialize by {
      have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len());
      have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
      have bytes.as_ptr() == old(bytes.as_ptr());
      have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
      have bytes.len() == old(bytes.len() - bytes.len() % 4u64);
      have a <= 65520u32;
      have b <= 65520u32;
      have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
      have remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
      have loop(0).iter.chunk_size == 22208u64;
      have remainder_chunk.len() == (bytes.len()) % 22208u64;
      have remainder.len() == old(bytes.len() % 4u64);
      have to_integer(a_vec.0[0]) <= 65520;
      have to_integer(a_vec.0[1]) <= 65520;
      have to_integer(a_vec.0[2]) <= 65520;
      have to_integer(a_vec.0[3]) <= 65520;
      have to_integer(b_vec.0[0]) <= 65520;
      have to_integer(b_vec.0[1]) <= 65520;
      have to_integer(b_vec.0[2]) <= 65520;
      have to_integer(b_vec.0[3]) <= 65520;
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a));
      have 0 <= old(to_integer((self.b as u32)));
      have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32))));
      have loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by close();
      have to_integer(loop(0).iter.len()) + iterations == to_integer((bytes.len()) / 22208u64);
     }
     maintain by {
      mark outer_pass;
      if loop(0).iter.chunk_size <= loop(0).iter.v.len() {
       have loop(0).iter.chunk_size == 22208u64;
       have 22208u64 <= loop(0).iter.v.len();
       have to_integer(22208u64) <= to_integer(loop(0).iter.v.len());
       apply(integer::positive_divisor_quotient_lower(to_integer(loop(0).iter.v.len()), to_integer(22208u64), 1));
       apply(integer::uint64_divide_to_integer(loop(0).iter.v.len(), 22208u64));
       have 0u64 < loop(0).iter.len() by close();
      have loop(0).iter.len() <= (bytes.len()) / 22208u64 by close() using { to_integer(loop(0).iter.len()) + iterations == to_integer((bytes.len()) / 22208u64); 0 <= iterations; };
      apply(integer::uint64_subtract_to_integer((bytes.len()) / 22208u64, loop(0).iter.len()));
      have to_integer(((bytes.len()) / 22208u64 - loop(0).iter.len())) == iterations by close() using { to_integer(((bytes.len()) / 22208u64 - loop(0).iter.len())) == to_integer((bytes.len()) / 22208u64) - to_integer(loop(0).iter.len()); to_integer(loop(0).iter.len()) + iterations == to_integer((bytes.len()) / 22208u64); };
      have loop(0).iter.chunk_size == 22208u64;
      apply(adler_chunk_bytes_next_22208(loop(0).iter.len(), (bytes.len())));
      apply(adler_chunk_bytes_offset_22208(loop(0).iter.len(), (bytes.len())));
      have 22208u64 <= adler_chunk_bytes(loop(0).iter.len(), 22208u64);
      have 0u64 < adler_chunk_bytes(loop(0).iter.len(), 22208u64) by close() using { 22208u64 <= adler_chunk_bytes(loop(0).iter.len(), 22208u64); };
      // The first fact about the batch pointer is its offset from `bytes`; the inner loop takes its
      // view of the batch out of the input's view at that offset.
      have loop(0).iter.v == (bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) by {
       have loop(0).iter.v == bytes.as_ptr() + ((bytes.len()) / 22208u64 - loop(0).iter.len()) * 22208u64 by close();
       rewrite(to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(((bytes.len()) / 22208u64 - loop(0).iter.len()) * 22208u64));
       close();
      }
      apply(integer::uint64_subtract_to_integer(((bytes.len()) - (bytes.len()) % 22208u64), adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
      have to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22208 <= to_integer(bytes.len()) by close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) - to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)); 22208u64 <= adler_chunk_bytes(loop(0).iter.len(), 22208u64); to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len()); };
      have to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) < to_integer(bytes.len()) by close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22208 <= to_integer(bytes.len()); };
      have to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + to_integer(22207u64) <= 18446744073709551615 by close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22208 <= to_integer(bytes.len()); };
      apply(integer::uint64_add_to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), 22207u64));
      have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22207u64) < to_integer(bytes.len()) by close() using { to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22207u64) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + to_integer(22207u64); to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) + 22208 <= to_integer(bytes.len()); };
      mark outer_head;
      have at(outer_head, loop(0).iter.v) == at(outer_head, (bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))));
      have at(outer_head, loop(0).iter.chunk_size) == 22208u64;
      have 0u64 < at(outer_head, loop(0).iter.len());
      have to_integer(adler_chunk_bytes(at(outer_head, loop(0).iter.len()) - 1u64, 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64);
      have to_integer(at(outer_head, loop(0).iter.len())) + iterations == to_integer((bytes.len()) / 22208u64);
      have to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
      have at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) % 22208u64 == 0u64;
      have 22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      have at(outer_head, (bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) == bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
      step_until(loop(1).entry);
      have chunk.len() == 22208u64;

      have chunk.as_ptr() == at(outer_head, (bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))));
      have loop(0).iter.v == at(outer_head, loop(0).iter.v) + 22208u64 by close();
      have 22208u64 <= at(outer_head, loop(0).iter.v.len());
      apply(integer::uint64_subtract_to_integer(at(outer_head, loop(0).iter.v.len()), 22208u64));
      have loop(0).iter.v.len() == at(outer_head, loop(0).iter.v.len()) - 22208u64 by close();
      have loop(0).iter.len() == at(outer_head, loop(0).iter.len()) - 1u64;
      have loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      have to_integer(loop(0).iter.len()) + (iterations + 1) == to_integer((bytes.len()) / 22208u64) by close() using { loop(0).iter.len() == at(outer_head, loop(0).iter.len()) - 1u64; 0u64 < at(outer_head, loop(0).iter.len()); to_integer(at(outer_head, loop(0).iter.len())) + iterations == to_integer((bytes.len()) / 22208u64); };
      have loop(0).iter.len() <= (bytes.len()) / 22208u64;
      // Inside the inner loop `iterations` counts its passes, so the outer iterator's
      // position is carried there by its length.
      have (to_integer((bytes.len()) / 22208u64) - to_integer(loop(0).iter.len())) == iterations + 1 by close() using { to_integer(loop(0).iter.len()) + (iterations + 1) == to_integer((bytes.len()) / 22208u64); };
      have loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by close();
      // The inner iterator covers this 22208-byte chunk in 5552 four-byte chunks.
      have loop(1).iter.v == chunk.as_ptr();
      have loop(1).iter.chunk_size == 4u64;
      have loop(1).iter.len() == chunk.len() / 4u64 by close();
      have chunk.len() % 4u64 == 0u64 by { rewrite(chunk.len(), 22208u64); close(); }
      apply(adler_chunk_bytes_whole_4(chunk.len()));
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) == chunk.len() by { rewrite(loop(1).iter.len(), chunk.len() / 4u64); close(); }
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) == 22208u64 by close() using { adler_chunk_bytes(loop(1).iter.len(), 4u64) == chunk.len(); chunk.len() == 22208u64; };
      have loop(1).iter.len() <= chunk.len() / 4u64;
     have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) == 22208 by { rewrite(adler_chunk_bytes(loop(1).iter.len(), 4u64), 22208u64); close(); }
      have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == chunk by { rewrite(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32), 22208); close(); }
     have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64) by { rewrite(loop(0).iter.len(), at(outer_head, loop(0).iter.len()) - 1u64); close(); }
     apply(adler_outer_remaining_step_divisible_u64(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))));
     have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64 by { rewrite(to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64)); close(); }

      have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len()));
       to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64);
       22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
      };
      have to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(bytes.len()) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len()));  to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len()); };
      have to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len()));
       22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len());
      };
      have chunk.as_ptr() == bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) by { rewrite(chunk.as_ptr(), at(outer_head, (bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); close(); }
      have to_integer(22208u64) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len()));
       to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64);
       to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
       22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
      };
      have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) == to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len()));
       to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64);
       to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
       22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
       to_integer(22208u64) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      };
      have chunk.as_ptr() == bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) by { rewrite(to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)), to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); close(); }
      have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) <= to_integer(bytes.len()) by { rewrite(to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)), to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); close(); }
      have to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) by { rewrite(to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)), to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); close(); }
      mark outer_chunk;
      // The batch continues the uint64 running prefix at the batch cursor.
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(a)) by close();
      have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer(a), old(to_integer((self.b as u32)))) by close();
      have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) by { rewrite(adler_chunk_bytes(loop(1).iter.len(), 4u64), 22208u64); close(); }
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a)) by { rewrite(to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)), to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); close(); }
      have chunk == at(outer_chunk, chunk.as_ptr());
      have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(outer_chunk, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      have (bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) == at(outer_chunk, (bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))));
     apply(adler_lane_initial_ceiling());
     apply(adler_lane_iterator_initial(22208));
     have adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == 0 by { rewrite(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32), 22208); close(); }
     have to_integer(a_vec.0[0]) <= 65520;
     have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[0]) <= 65520; }; }
     have to_integer(b_vec.0[0]) <= 65520;
     have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[0]) <= 65520; }; }
     have to_integer(a_vec.0[1]) <= 65520;
     have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[1]) <= 65520; }; }
     have to_integer(b_vec.0[1]) <= 65520;
     have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[1]) <= 65520; }; }
     have to_integer(a_vec.0[2]) <= 65520;
     have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[2]) <= 65520; }; }
     have to_integer(b_vec.0[2]) <= 65520;
     have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[2]) <= 65520; }; }
     have to_integer(a_vec.0[3]) <= 65520;
     have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[3]) <= 65520; }; }
     have to_integer(b_vec.0[3]) <= 65520;
     have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[3]) <= 65520; }; }
     have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) by { rewrite(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32), 22208); close() using {}; }
     have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208 by { rewrite(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32), 22208); close() using {}; }
     have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208 by close();
     have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by { rewrite(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32), 22208); close() using {}; }
     have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == at(outer_chunk, chunk.as_ptr()) + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32));
     have chunk.len() < 22209u64;
     have chunk.len() == 22208u64 by close();
     have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64;
     have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by {
      rewrite((chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))), chunk.as_ptr());
      rewrite(adler_chunk_bytes(loop(1).iter.len(), 4u64), 22208u64);
      rewrite(chunk.as_ptr(), bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)); close();
     }
     have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); };
     have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) <= to_integer(bytes.len()) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len()); };
     have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) <= to_integer(18446744073709529407u64) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len())); 22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)); to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); };
     have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) == to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) + 22208u64) by close() using { to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64); 22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)); bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); };
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
     apply(adler_canonical_lane_b_floor(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])));
     have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { apply(adler_empty_full_batch_position(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); rewrite(to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), 0); have to_integer(b) + 0 * to_integer(a) == to_integer(b) by close() using {}; rewrite(to_integer(b) + 0 * to_integer(a), to_integer(b)); close(); }
     apply(adler_empty_full_batch_position(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)), to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64))))); rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))), 0); have to_integer(b) + 0 * to_integer(a) == to_integer(b) by close() using {}; rewrite(to_integer(b) + 0 * to_integer(a), to_integer(b)); close(); }
     have defined(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32));
     loop {
      decreases loop(1).iter.len();
      invariant loop(1).iter.chunk_size == 4u64;
      invariant loop(1).iter.v.len() == adler_chunk_bytes(loop(1).iter.len(), 4u64);
     invariant adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64;
     invariant to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
     invariant to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len());
      owns a_vec.0[0..4];
      owns b_vec.0[0..4];
      views bytes[0..(bytes.len())];
      invariant (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64));
      invariant to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
      invariant chunk.as_ptr() == bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64);
      invariant to_integer(22208u64) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      invariant to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) <= to_integer(bytes.len());
      invariant to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64));
      invariant chunk.len() == 22208u64;
      invariant chunk == at(loop(1).entry, chunk.as_ptr());
      invariant bytes.as_ptr() == old(bytes.as_ptr());
     invariant forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
      invariant bytes.len() == old(bytes.len() - bytes.len() % 4u64);
      invariant adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(loop(1).entry, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      invariant adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
      invariant remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
     invariant loop(0).iter.chunk_size == 22208u64;
      invariant remainder_chunk.len() == (bytes.len()) % 22208u64;
      invariant remainder.len() == old(bytes.len() % 4u64);
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
      invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a));
      invariant 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
      invariant loop(0).iter.len() == at(loop(1).entry, loop(0).iter.len());
      invariant loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
      invariant loop(1).iter.v == chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64));
      invariant to_integer(loop(1).iter.len()) + iterations == to_integer(chunk.len() / 4u64);

      initialize by {
       have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64;
       have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
       have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len());
       have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by { close(); close(); }
       have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
       have chunk.as_ptr() == bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64);
       have to_integer(22208u64) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) <= to_integer(bytes.len());
       have to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64));
       have chunk.len() == 22208u64;
       have chunk == at(loop(1).entry, chunk.as_ptr());
       have bytes.as_ptr() == old(bytes.as_ptr());
       have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
       have bytes.len() == old(bytes.len() - bytes.len() % 4u64);
       have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(loop(1).entry, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
       have remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
       have loop(0).iter.chunk_size == 22208u64;
       have remainder_chunk.len() == (bytes.len()) % 22208u64;
       have remainder.len() == old(bytes.len() % 4u64);
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
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a));
       have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
       have 0 <= old(to_integer((self.b as u32)));
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
       have loop(0).iter.len() == at(loop(1).entry, loop(0).iter.len());
       have loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       have loop(1).iter.v == chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by close();
       have to_integer(loop(1).iter.len()) + iterations == to_integer(chunk.len() / 4u64);
      }
     maintain by {
       mark inner_pass;
       if loop(1).iter.chunk_size <= loop(1).iter.v.len() {
        have loop(1).iter.chunk_size == 4u64;
        have 4u64 <= loop(1).iter.v.len();
        have to_integer(4u64) <= to_integer(loop(1).iter.v.len());
        apply(integer::positive_divisor_quotient_lower(to_integer(loop(1).iter.v.len()), to_integer(4u64), 1));
        apply(integer::uint64_divide_to_integer(loop(1).iter.v.len(), 4u64));
        have 0u64 < loop(1).iter.len() by close();
        have loop(1).iter.len() <= chunk.len() / 4u64 by close() using { to_integer(loop(1).iter.len()) + iterations == to_integer(chunk.len() / 4u64); 0 <= iterations; };
        apply(integer::uint64_subtract_to_integer(chunk.len() / 4u64, loop(1).iter.len()));
        have to_integer((chunk.len() / 4u64 - loop(1).iter.len())) == iterations by close() using { to_integer((chunk.len() / 4u64 - loop(1).iter.len())) == to_integer(chunk.len() / 4u64) - to_integer(loop(1).iter.len()); to_integer(loop(1).iter.len()) + iterations == to_integer(chunk.len() / 4u64); };
        have loop(1).iter.chunk_size == 4u64;
        apply(adler_chunk_bytes_next_4(loop(1).iter.len(), chunk.len()));
        have chunk.len() % 4u64 == 0u64 by { rewrite(chunk.len(), 22208u64); close(); }
        apply(adler_chunk_bytes_offset_whole_4(loop(1).iter.len(), chunk.len()));
        have 4u64 <= adler_chunk_bytes(loop(1).iter.len(), 4u64);
        have 4 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) by {
         have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 2147483647u64 by close() using { adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64; };
         apply(adler_bounded_count_lower(adler_chunk_bytes(loop(1).iter.len(), 4u64), 4));
         close();
        }
        have 4u64 <= adler_chunk_bytes(loop(1).iter.len(), 4u64);
        have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); };
        have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(bytes.len()) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len()); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer(bytes.len()) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(bytes.len()); };
        have to_integer(4u64) <= to_integer(bytes.len() - ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) <= to_integer(bytes.len()); 4u64 <= adler_chunk_bytes(loop(1).iter.len(), 4u64); };
        // The first fact about the chunk's pointer is its offset from `bytes`: the helper call
        // below reads the chunk through the input's view, and the view is found by that fact.
        have loop(1).iter.v == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by {
         have loop(1).iter.v == chunk.as_ptr() + (chunk.len() / 4u64 - loop(1).iter.len()) * 4u64 by close();
         have loop(1).iter.v == chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by {
          rewrite(to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer((chunk.len() / 4u64 - loop(1).iter.len()) * 4u64));
          close();
         }
         apply(integer::uint64_subtract_to_integer(chunk.len(), adler_chunk_bytes(loop(1).iter.len(), 4u64)));
         apply(integer::uint64_subtract_to_integer(((bytes.len()) - (bytes.len()) % 22208u64), adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
         apply(integer::uint64_subtract_to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), 22208u64));
         apply(integer::uint64_subtract_to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), adler_chunk_bytes(loop(1).iter.len(), 4u64)));
         have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by close() using { to_integer(chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(chunk.len()) - to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - to_integer(22208u64); to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); chunk.len() == 22208u64; };
         have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= 18446744073709551615 by close() using { to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer(bytes.len()); };
         apply(integer::uint64_add_to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64), (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))));
         have chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by { rewrite(chunk.as_ptr(), bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)); close() using { to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= 18446744073709551615; to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))); }; }
         have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by close() using { to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
         rewrite(to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))));
         close() using { loop(1).iter.v == chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)); chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        }
        apply(integer::uint64_subtract_to_integer(chunk.len(), adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        apply(integer::uint64_subtract_to_integer(((bytes.len()) - (bytes.len()) % 22208u64), adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
        apply(integer::uint64_subtract_to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), 22208u64));
        apply(integer::uint64_subtract_to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by close() using { to_integer(chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(chunk.len()) - to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - to_integer(22208u64); to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); chunk.len() == 22208u64; };
        have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= 18446744073709551615 by close() using { to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer(bytes.len()); };
        apply(integer::uint64_add_to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64), (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))));
        have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) by close() using { to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        apply(integer::uint64_subtract_to_integer(bytes.len(), ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))));
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()) by close() using { to_integer(4u64) <= to_integer(bytes.len() - ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer(bytes.len() - ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(bytes.len()) - to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) < to_integer(bytes.len()) by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(3u64) <= 18446744073709551615 by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        apply(integer::uint64_add_to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)), 3u64));
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) + 3u64) < to_integer(bytes.len()) by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) + 3u64) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(3u64); to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) < to_integer(bytes.len()) by close() using { to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64) + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) < to_integer(bytes.len()); };
        have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 3 < to_integer(bytes.len()) by close() using { to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) + to_integer((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        // The inner loop views the aligned prefix only: bound the chunk inside it.
        have to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len())) by close();
        apply(integer::uint64_subtract_to_integer((bytes.len()), (bytes.len()) % 22208u64));
        have 0 <= to_integer((bytes.len()) % 22208u64);
        have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer((bytes.len())) by close() using { to_integer((bytes.len()) - (bytes.len()) % 22208u64) == to_integer((bytes.len())) - to_integer((bytes.len()) % 22208u64); 0 <= to_integer((bytes.len()) % 22208u64); };
        have 0 <= to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer((bytes.len())) by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) - to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)); 4u64 <= adler_chunk_bytes(loop(1).iter.len(), 4u64); to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer((bytes.len())); 0 <= to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) < to_integer((bytes.len())) by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer((bytes.len())); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) + 3u64) < to_integer((bytes.len())) by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) + 3u64) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(3u64); to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) + to_integer(4u64) <= to_integer((bytes.len())); };
        // The same chunk starts `chunk.len() - remaining` bytes into the batch, where the old cursor stood.
        have loop(1).iter.v == chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by {
         have loop(1).iter.v == chunk.as_ptr() + (chunk.len() / 4u64 - loop(1).iter.len()) * 4u64 by close();
         rewrite(to_integer(chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)), to_integer((chunk.len() / 4u64 - loop(1).iter.len()) * 4u64));
         close();
        }
        have chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64 by close() using { adler_chunk_bytes(loop(1).iter.len(), 4u64) <= chunk.len(); chunk.len() == 22208u64; };
        apply(adler_count_byte_pointer(chunk, chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        have chunk.len() <= 22208u64 by close() using { chunk.len() == 22208u64; };
        apply(adler_count_step(chunk.len(), adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        have ((chunk.len() as u32) as i32) == 22208 by { rewrite(chunk.len(), 22208u64); close(); }
        have to_integer((((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) as uint32) as int32)) == to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by {
         rewrite(to_integer((((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) as uint32) as int32)), to_integer(((chunk.len() as uint32) as int32) - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
         rewrite(((chunk.len() as uint32) as int32), 22208);
         close();
        }
        have loop(1).iter.v == (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by {
         rewrite(to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), to_integer((((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) as uint32) as int32)));
         close() using { loop(1).iter.v == chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)); chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == chunk.as_ptr() + (((chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64)) as uint32) as int32); };
        }
        mark lane_head;
        have at(lane_head, loop(1).iter.v) == at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have at(lane_head, loop(1).iter.chunk_size) == 4u64;
        have 0u64 < at(lane_head, loop(1).iter.len());
        have to_integer(adler_chunk_bytes(at(lane_head, loop(1).iter.len()) - 1u64, 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64);
        have to_integer(at(lane_head, loop(1).iter.len())) + iterations == to_integer(chunk.len() / 4u64);
        have at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) % 4 == 0;
        have at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208;
        have 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32));
        have 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32));
        have 22208 <= 22208 by close() using { 22208 <= 22208; };
        have at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) == at(loop(1).entry, chunk.as_ptr()) + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have 0 <= to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { 0 <= 22208; 22208 <= 22208; 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; };
        have to_integer((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) + 4) <= 22208 by close() using { 0 <= 22208; 22208 <= 22208; 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; };
        step_until(loop(1).statement(0).entry);
        have byte_vec.as_ptr() == at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have byte_vec.len() == 4u64;
        have loop(1).iter.v == at(lane_head, loop(1).iter.v) + 4u64 by close();
        have 4u64 <= at(lane_head, loop(1).iter.v.len());
        apply(integer::uint64_subtract_to_integer(at(lane_head, loop(1).iter.v.len()), 4u64));
        have loop(1).iter.v.len() == at(lane_head, loop(1).iter.v.len()) - 4u64 by close();
        have loop(1).iter.len() == at(lane_head, loop(1).iter.len()) - 1u64;
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64) by { rewrite(loop(1).iter.len(), at(lane_head, loop(1).iter.len()) - 1u64); close(); }
        have 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= 22208u64;
        apply(integer::uint64_subtract_to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)), 4u64));
        have adler_chunk_bytes(loop(1).iter.len(), 4u64) == at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64 by close() using { to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64); to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) - to_integer(4u64); };
        apply(adler_count_lane_step(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))));
        have byte_vec.as_ptr() == at(loop(1).entry, chunk.as_ptr()) + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by { rewrite(byte_vec.as_ptr(), at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))))); close(); }
        have byte_vec.as_ptr() == chunk.as_ptr() + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4);
        have 0 <= 22208 by close();
        have 22208 <= 22208 by close();
        have 22208 <= 22208 by close() using { 22208 == 22208; 22208 <= 22208; };
        have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using {
          to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4);
          4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32));
          at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208;
         };
        have 0 <= to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) by { rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); close(); }
        have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) <= 22208 by close() using { 22208 <= 22208; 0 <= 22208; 22208 <= 22208; to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 0 <= 22208; 22208 <= 22208; 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; };
        have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) <= to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by close() using { 22208 == 22208; to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 0 <= 22208; 22208 <= 22208; 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 0 <= to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)); to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) <= 22208; 0 <= 22208; 22208 <= 22208; };
        have byte_vec.as_ptr() == chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4);
        have to_integer((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) <= 22204 by close() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; };
        // The helper reads the chunk through the input's view: place its pointer in `bytes`.
        have at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        have byte_vec.as_ptr() == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) by close() using { byte_vec.as_ptr() == byte_vec.as_ptr(); byte_vec.as_ptr() == at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) <= to_integer(bytes.len());
        have to_integer(4u64) <= to_integer(bytes.len() - ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))));
        apply(integer::uint64_subtract_to_integer(bytes.len(), ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))));
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615 by close() using { to_integer(4u64) <= to_integer(bytes.len() - ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); to_integer(bytes.len() - ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) == to_integer(bytes.len()) - to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); };
        apply(integer::uint64_add_to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), 4u64));
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) <= to_integer(bytes.len()) by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64); to_integer(4u64) <= to_integer(bytes.len() - ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); to_integer(bytes.len() - ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) == to_integer(bytes.len()) - to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); };
        have byte_vec.as_ptr() == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) by close() using { byte_vec.as_ptr() == byte_vec.as_ptr(); byte_vec.as_ptr() == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) < to_integer(bytes.len()) by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64); to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) <= to_integer(bytes.len()); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(3u64) <= 18446744073709551615 by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615; };
        apply(integer::uint64_add_to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), 3u64));
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 3u64) < to_integer(bytes.len()) by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 3u64) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(3u64); to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64); to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) <= to_integer(bytes.len()); };
        mark before_from;
        // The helper call is one simple step of its own.
        step_until(loop(1).statement(1).entry);
        have to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4);
        mark vector_a;
        // Connect the actual constructor bytes to the input at the uint64 cursor.
        // Prove machine equality before rewriting an Integer observation;
        // pointer rewriting inside an observation exposes different retained_states.
        have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) <= 22204 by { rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); close() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; }; }
        have at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)));
        have to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len())); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + 4 <= 18446744073709551615 by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64); };
        have at(vector_a, byte_vec.as_ptr()) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) by close() using { byte_vec.as_ptr() == at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        have at(before_from, byte_vec.as_ptr()) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) by close() using { byte_vec.as_ptr() == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))); };
        have to_integer(at(vector_a, val.0[0])) == at(before_from, to_integer((byte_vec[0] as i32))) by close() using { to_integer(val.0[0]) == at(before_from, to_integer((byte_vec[0] as i32))); };
        have at(before_from, (byte_vec[0] as i32)) == at(before_from, ((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32)) by {
         rewrite(at(before_from, byte_vec.as_ptr()), bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); close();
        }
        have to_integer(at(vector_a, val.0[0])) == at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[0])), at(before_from, to_integer((byte_vec[0] as i32))));
         rewrite(at(before_from, (byte_vec[0] as i32)), at(before_from, ((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32)));
         close();
        }
        have at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32))) == at(vector_a, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32))) by close();
        have to_integer(at(vector_a, val.0[0])) == at(vector_a, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[0])), at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[0] as i32)))); close();
        }
        have to_integer(at(vector_a, val.0[1])) == at(before_from, to_integer((byte_vec[1] as i32))) by close() using { to_integer(val.0[1]) == at(before_from, to_integer((byte_vec[1] as i32))); };
        have at(before_from, (byte_vec[1] as i32)) == at(before_from, ((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32)) by {
         rewrite(at(before_from, byte_vec.as_ptr()), bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); close();
        }
        have to_integer(at(vector_a, val.0[1])) == at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[1])), at(before_from, to_integer((byte_vec[1] as i32))));
         rewrite(at(before_from, (byte_vec[1] as i32)), at(before_from, ((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32)));
         close();
        }
        have at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32))) == at(vector_a, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32))) by close();
        have to_integer(at(vector_a, val.0[1])) == at(vector_a, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[1])), at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[1] as i32)))); close();
        }
        have to_integer(at(vector_a, val.0[2])) == at(before_from, to_integer((byte_vec[2] as i32))) by close() using { to_integer(val.0[2]) == at(before_from, to_integer((byte_vec[2] as i32))); };
        have at(before_from, (byte_vec[2] as i32)) == at(before_from, ((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32)) by {
         rewrite(at(before_from, byte_vec.as_ptr()), bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); close();
        }
        have to_integer(at(vector_a, val.0[2])) == at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[2])), at(before_from, to_integer((byte_vec[2] as i32))));
         rewrite(at(before_from, (byte_vec[2] as i32)), at(before_from, ((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32)));
         close();
        }
        have at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32))) == at(vector_a, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32))) by close();
        have to_integer(at(vector_a, val.0[2])) == at(vector_a, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[2])), at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[2] as i32)))); close();
        }
        have to_integer(at(vector_a, val.0[3])) == at(before_from, to_integer((byte_vec[3] as i32))) by close() using { to_integer(val.0[3]) == at(before_from, to_integer((byte_vec[3] as i32))); };
        have at(before_from, (byte_vec[3] as i32)) == at(before_from, ((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32)) by {
         rewrite(at(before_from, byte_vec.as_ptr()), bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); close();
        }
        have to_integer(at(vector_a, val.0[3])) == at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[3])), at(before_from, to_integer((byte_vec[3] as i32))));
         rewrite(at(before_from, (byte_vec[3] as i32)), at(before_from, ((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32)));
         close();
        }
        have at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32))) == at(vector_a, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32))) by close();
        have to_integer(at(vector_a, val.0[3])) == at(vector_a, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[3])), at(before_from, to_integer(((bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))))[3] as i32)))); close();
        }
        have 0 <= to_integer(at(vector_a, a_vec.0[0]));
        have 0 <= to_integer(at(vector_a, b_vec.0[0]));
        have to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, val.0[0]));
        have to_integer(at(vector_a, val.0[0])) <= 255;
        apply(adler_lane_iterator_add_contracts(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, val.0[0])));
        apply(adler_lane_iterator_native_preservation(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, val.0[0])));
        have 0 <= to_integer(at(vector_a, a_vec.0[1]));
        have 0 <= to_integer(at(vector_a, b_vec.0[1]));
        have to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, val.0[1]));
        have to_integer(at(vector_a, val.0[1])) <= 255;
        apply(adler_lane_iterator_add_contracts(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, val.0[1])));
        apply(adler_lane_iterator_native_preservation(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, val.0[1])));
        have 0 <= to_integer(at(vector_a, a_vec.0[2]));
        have 0 <= to_integer(at(vector_a, b_vec.0[2]));
        have to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, val.0[2]));
        have to_integer(at(vector_a, val.0[2])) <= 255;
        apply(adler_lane_iterator_add_contracts(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, val.0[2])));
        apply(adler_lane_iterator_native_preservation(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, val.0[2])));
        have 0 <= to_integer(at(vector_a, a_vec.0[3]));
        have 0 <= to_integer(at(vector_a, b_vec.0[3]));
        have to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, val.0[3]));
        have to_integer(at(vector_a, val.0[3])) <= 255;
        apply(adler_lane_iterator_add_contracts(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[3])));
        apply(adler_lane_iterator_native_preservation(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[3])));
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(vector_a, bytes.as_ptr()), ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(a)) by { close(); }
        have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) by { have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); }; rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); close(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[0]), at(vector_a, val.0[0])));
        have to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0])), to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))); close(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[1]), at(vector_a, val.0[1])));
        have to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))); close(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[2]), at(vector_a, val.0[2])));
        have to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))); close(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[3]), at(vector_a, val.0[3])));
        have to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3])), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))); close(); }
        apply(adler_native_deferred_b_step((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[0]), at(vector_a, val.0[1]), at(vector_a, val.0[2]), at(vector_a, val.0[3])));
        apply(adler_nonnegative_deferred_b_step((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[0]), at(vector_a, val.0[1]), at(vector_a, val.0[2]), at(vector_a, val.0[3])));
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b_u64(at(vector_a, bytes.as_ptr()), ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(at(vector_a, a)), old(to_integer((self.b as u32)))) by { have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); }; rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); close(); }
        apply(adler_native_deferred_b_prefix_step_u64(at(vector_a, bytes.as_ptr()), ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4), to_integer(a), old(to_integer((self.b as u32))), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[0]), at(vector_a, val.0[1]), at(vector_a, val.0[2]), at(vector_a, val.0[3])));
        apply(adler_native_four_lane_a_prefix_step_u64(at(vector_a, bytes.as_ptr()), ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(a), to_integer(a), at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, val.0[0]), at(vector_a, val.0[1]), at(vector_a, val.0[2]), at(vector_a, val.0[3])));
        have to_integer(a_vec.0[0]) + to_integer(val.0[0]) <= 4294967295 by close() using { to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0])) <= 4294967295; };
        have to_integer(a_vec.0[1]) + to_integer(val.0[1]) <= 4294967295 by close() using { to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])) <= 4294967295; };
        have to_integer(a_vec.0[2]) + to_integer(val.0[2]) <= 4294967295 by close() using { to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])) <= 4294967295; };
        have to_integer(a_vec.0[3]) + to_integer(val.0[3]) <= 4294967295 by close() using { to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3])) <= 4294967295; };
        step_until(loop(1).statement(2).entry);
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]));
        have b_vec.0[0] == at(vector_a, b_vec.0[0]);
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])) by close() using { b_vec.0[0] == at(vector_a, b_vec.0[0]); };
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) by close() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])); };
        have to_integer(b_vec.0[0]) + to_integer(a_vec.0[0]) <= 4294967295 by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])); to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])); to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) <= 4294967295; };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]));
        have b_vec.0[1] == at(vector_a, b_vec.0[1]);
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])) by close() using { b_vec.0[1] == at(vector_a, b_vec.0[1]); };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); };
        have to_integer(b_vec.0[1]) + to_integer(a_vec.0[1]) <= 4294967295 by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) <= 4294967295; };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]));
        have b_vec.0[2] == at(vector_a, b_vec.0[2]);
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])) by close() using { b_vec.0[2] == at(vector_a, b_vec.0[2]); };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); };
        have to_integer(b_vec.0[2]) + to_integer(a_vec.0[2]) <= 4294967295 by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) <= 4294967295; };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]));
        have b_vec.0[3] == at(vector_a, b_vec.0[3]);
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])) by close() using { b_vec.0[3] == at(vector_a, b_vec.0[3]); };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); };
        have to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]) <= 4294967295 by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) <= 4294967295; };
        mark vector_b;
        step_until(loop.back_edge);
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]));
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])));
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) by close() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))) by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]));
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))) by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]));
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))) by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]));
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))) by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); };
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208 by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; };
        have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208 by close();
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by { rewrite(to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)), to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4)); close() using { at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) % 4 == 0; 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; }; }
        have to_integer((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) + 4) == to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; };
        have 0 <= to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; };
        have to_integer(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) <= 22204 by close() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; };
        have 0 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by close() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); };
        have defined(22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have (at(loop(1).entry, chunk.as_ptr()) + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) + 4 == at(loop(1).entry, chunk.as_ptr()) + ((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) + 4) by apply(adler_bounded_pointer_association(at(loop(1).entry, chunk.as_ptr()), 22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))));
        have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == at(loop(1).entry, chunk.as_ptr()) + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by close() using { chunk == at(loop(1).entry, chunk.as_ptr()); };
        // The cursor term advanced by four bytes with the count.
        have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) + 4 by { rewrite((chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))), at(loop(1).entry, chunk.as_ptr()) + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); rewrite(at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))), at(loop(1).entry, chunk.as_ptr()) + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); rewrite((at(loop(1).entry, chunk.as_ptr()) + (22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))) + 4, at(loop(1).entry, chunk.as_ptr()) + ((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) + 4)); rewrite(to_integer((22208 - at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) + 4), to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); close() using {}; }
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) < at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; 22208 <= 22208; };
        have chunk.len() == 22208u64 by close();
        have chunk == at(loop(1).entry, chunk.as_ptr()) by close();
        have bytes.as_ptr() == old(bytes.as_ptr()) by close();
        have bytes.len() == old(bytes.len() - bytes.len() % 4u64) by close();
        have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(loop(1).entry, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by close();
        have (bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) == at(loop(1).entry, (bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)))) by close();
        have remainder_chunk.len() == (bytes.len()) % 22208u64 by close();
        have remainder.len() == old(bytes.len() % 4u64) by close();
        have chunk.len() == 22208u64 by close();
        have a <= 65520u32 by close();
        have b <= 65520u32 by close();
        have 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208 by close();
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by close();
        have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == at(loop(1).entry, chunk.as_ptr()) + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) by close();
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64);
        have 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= 22208u64;
        have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64 by close() using {
         to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64);
         4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64));
         at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= 22208u64;
        };
        have adler_chunk_bytes(loop(1).iter.len(), 4u64) < at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) by close() using {
         to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64);
         4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64));
         at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= 22208u64;
        };
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64);
        have 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) by close();
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) by close() using { to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64) by close() using { bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)); };
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615 by close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64); };
        apply(integer::uint64_add_to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))), 4u64));
        have byte_vec.as_ptr() + 4 == bytes.as_ptr() + (((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) by { rewrite(byte_vec.as_ptr(), bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))); close() using { to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615; to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)))) + to_integer(4u64); }; }
        have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == byte_vec.as_ptr() + 4 by { rewrite(byte_vec.as_ptr(), at(lane_head, (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))))); close(); }
        have to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))) == to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64) by close() using { to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); bytes.len() % 4u64 <= bytes.len(); to_integer((bytes.len()) % 22208u64) <= to_integer(bytes.len()); to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64)); };
        have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) by { rewrite(to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64)); close() using { (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == byte_vec.as_ptr() + 4; byte_vec.as_ptr() + 4 == bytes.as_ptr() + (((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64); }; }
        have defined(22208 - (((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) by close() using { 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32); ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22208; };
        // Retain the exact A transition at the actual inner back edge.
        have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 22204 by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 22208; };
        apply(adler_full_batch_within_advance(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a)) by {
         rewrite(to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64));
         rewrite(to_integer(a_vec.0[0]), to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])));
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
         close();
        }
        have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by { rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4), to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); close(); }
        have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by {
         have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by close() using { to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4); };
         rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))), to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4));
         have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); };
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
         have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); };
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
         have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); };
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
         have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))) by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))); };
         rewrite(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))));
         have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))) by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))); };
         rewrite(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))));
         have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))) by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))); };
         rewrite(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))));
         have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))) by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))); };
         rewrite(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))));
         close();
        }
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32)))) by {
         rewrite(to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))), to_integer(((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - at(lane_head, adler_chunk_bytes(loop(1).iter.len(), 4u64))) + 4u64));
         have to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by close() using { to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4); };
         rewrite(to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))), to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) - 4) + 4));
         have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); };
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
         have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); };
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
         have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); };
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
         have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))) by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))); };
         rewrite(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))));
         have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))) by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))); };
         rewrite(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))));
         have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))) by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))); };
         rewrite(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))));
         have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))) by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))); };
         rewrite(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))));
         close();
        }
        // The invariants at the back edge, one pass further on.
        have loop(0).iter.len() == at(loop(1).entry, loop(0).iter.len());
        have loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have loop(1).iter.v == chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have to_integer(loop(1).iter.len()) + (iterations + 1) == to_integer(chunk.len() / 4u64) by close() using { loop(1).iter.len() == at(lane_head, loop(1).iter.len()) - 1u64; 0u64 < at(lane_head, loop(1).iter.len()); to_integer(at(lane_head, loop(1).iter.len())) + iterations == to_integer(chunk.len() / 4u64); };
        have loop(1).iter.len() <= chunk.len() / 4u64;
        // Every invariant at the back edge.
        have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64;
        have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
        have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len());
        have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
        have chunk.as_ptr() == bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64);
        have to_integer(22208u64) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) <= to_integer(bytes.len());
        have to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64));
        have chunk.len() == 22208u64;
        have chunk == at(loop(1).entry, chunk.as_ptr());
        have bytes.as_ptr() == old(bytes.as_ptr());
        have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
        have bytes.len() == old(bytes.len() - bytes.len() % 4u64);
        have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(loop(1).entry, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
        have remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
        have loop(0).iter.chunk_size == 22208u64;
        have remainder_chunk.len() == (bytes.len()) % 22208u64;
        have remainder.len() == old(bytes.len() % 4u64);
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
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a));
        have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
        have 0 <= old(to_integer((self.b as u32)));
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
        have loop(0).iter.len() == at(loop(1).entry, loop(0).iter.len());
        have loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have loop(1).iter.v == chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have to_integer(loop(1).iter.len()) + (iterations + 1) == to_integer(chunk.len() / 4u64);
        // The ranking members: the measure is read at the pass entry, before the header ran.
        have at(lane_head, loop(1).iter.len()) == at(inner_pass, loop(1).iter.len());
        have loop(1).iter.len() < at(lane_head, loop(1).iter.len()) by close() using { loop(1).iter.len() == at(lane_head, loop(1).iter.len()) - 1u64; 0u64 < at(lane_head, loop(1).iter.len()); };
        have loop(1).iter.len() < at(inner_pass, loop(1).iter.len()) by close() using { loop(1).iter.len() < at(lane_head, loop(1).iter.len()); at(lane_head, loop(1).iter.len()) == at(inner_pass, loop(1).iter.len()); };
       } else {
        // No chunk is left: the header test fails and the loop leaves by `break`.
        step();
        have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64;
        have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
        have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len());
        have (chunk.as_ptr() + (22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) <= to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
        have chunk.as_ptr() == bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64);
        have to_integer(22208u64) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64)) <= to_integer(bytes.len());
        have to_integer(22208u64) <= to_integer(bytes.len() - (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64) - 22208u64));
        have chunk.len() == 22208u64;
        have chunk == at(loop(1).entry, chunk.as_ptr());
        have bytes.as_ptr() == old(bytes.as_ptr());
        have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
        have bytes.len() == old(bytes.len() - bytes.len() % 4u64);
        have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == at(loop(1).entry, adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
        have remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
        have loop(0).iter.chunk_size == 22208u64;
        have remainder_chunk.len() == (bytes.len()) % 22208u64;
        have remainder.len() == old(bytes.len() % 4u64);
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
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a));
        have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
        have 0 <= old(to_integer((self.b as u32)));
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
        have loop(0).iter.len() == at(loop(1).entry, loop(0).iter.len());
        have loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
        have loop(1).iter.v == chunk.as_ptr() + (chunk.len() - adler_chunk_bytes(loop(1).iter.len(), 4u64));
        have to_integer(loop(1).iter.len()) + iterations == to_integer(chunk.len() / 4u64);
        step();
       }
      }
     }
      have loop(1).iter.len() == 0u64;
      apply(adler_chunk_bytes_none(4u64));
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) == 0u64 by { rewrite(loop(1).iter.len(), 0u64); close(); }
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) < 4u64 by close() using { adler_chunk_bytes(loop(1).iter.len(), 4u64) == 0u64; };
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 2147483647u64 by close() using { adler_chunk_bytes(loop(1).iter.len(), 4u64) <= 22208u64; };
      apply(adler_bounded_count(adler_chunk_bytes(loop(1).iter.len(), 4u64)));
      have to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) < to_integer(4) by close() using {
       to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64));
       to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) < to_integer(4u64);
      };
      have to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= to_integer(3) by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) < to_integer(4); };
      have (((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) <= 3;
      have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) < 4 by close() using { ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) <= 3; };
      have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) by close() using { 0 <= ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32); ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) < 4; };
      have ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) == 0 by close() using { ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == 0; ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) % 4 == ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32); };
      have to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)) == 0 by close() using { to_integer(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)) == to_integer(adler_chunk_bytes(loop(1).iter.len(), 4u64)); ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32) == 0; };
      have adler_chunk_bytes(loop(1).iter.len(), 4u64) == 0u64;
      have to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64)) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by { rewrite(adler_chunk_bytes(loop(1).iter.len(), 4u64), 0u64); close(); }
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a)) by { rewrite(to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); close(); }
      apply(adler_complete_full_batch_position(((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)));
      have 0 <= adler_lane_b(to_integer(b) + 22208 * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(22208, to_integer(22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32))); close(); }
      have truncating_remainder(adler_lane_b(to_integer(b) + 22208 * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(22208, to_integer((22208 - ((adler_chunk_bytes(loop(1).iter.len(), 4u64) as uint32) as int32)))); rewrite(to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)), to_integer((((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - adler_chunk_bytes(loop(1).iter.len(), 4u64))); close(); }
      mark full_lane_prefix;
      have truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(full_lane_prefix, bytes.as_ptr()), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(at(full_lane_prefix, a))) by close();
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
      apply(adler_lane_a_reduction(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))));
      have truncating_remainder(adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))), 65521) == adler_spec_b_u64(at(full_lane_prefix, bytes.as_ptr()), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(at(full_lane_prefix, a)), old(to_integer((self.b as u32)))) by close();
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
      have 0 <= to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by close() using { 0 <= to_integer(at(full_lane_prefix, b)); 0 <= to_integer(at(full_lane_prefix, a)); };
      have 0 <= adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))) by close();
      apply(adler_lane_b_reduction(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))));
      step_until(loop(0).statement(1).entry);
      have a <= 65520u32 by close() using { a <= 65520u32; };
      have to_integer(22208u32) * to_integer(a) <= 1455068160 by {
       rewrite(22208u32, 22208u32);
       close() using { to_integer(a) <= 65520; };
      }
      have to_integer(22208u32) * to_integer(a) <= 4294967295 by close() using { to_integer(22208u32) * to_integer(a) <= 1455068160; };
      apply(integer::uint32_multiply_guard_by_integer_bound(22208u32, a));
      apply(integer::uint32_multiply_to_integer(22208u32, a));
      mark full_product;
      have to_integer(at(full_product, 22208u32)) * to_integer(at(full_product, a)) <= 1455068160 by close() using { to_integer(22208u32) * to_integer(a) <= 1455068160; };
      have at(full_product, a) == 0u32 or at(full_product, 22208u32) <= 4294967295u32 / at(full_product, a) by close() using { a == 0u32 or 22208u32 <= 4294967295u32 / a; };
      apply(integer::uint32_multiply_to_integer(at(full_product, 22208u32), at(full_product, a)));
      have to_integer(at(full_product, (22208u32 * a))) == to_integer(at(full_product, 22208u32) * at(full_product, a));
      have to_integer(at(full_product, (22208u32 * a))) <= 1455068160 by {
       rewrite(to_integer(at(full_product, (22208u32 * a))), to_integer(at(full_product, 22208u32) * at(full_product, a)));
       rewrite(to_integer(at(full_product, 22208u32) * at(full_product, a)), to_integer(at(full_product, 22208u32)) * to_integer(at(full_product, a)));
       close();
      }
      have to_integer(b) + to_integer(at(full_product, (22208u32 * a))) <= 4294967295 by close() using { to_integer(b) <= 65520; to_integer(at(full_product, (22208u32 * a))) <= 1455068160; };
      have b <= 4294967295u32 - at(full_product, (22208u32 * a)) by close() using { to_integer(b) + to_integer(at(full_product, (22208u32 * a))) <= 4294967295; };
      apply(integer::uint32_add_to_integer(b, at(full_product, (22208u32 * a))));
      have to_integer(b + at(full_product, (22208u32 * a))) == to_integer(b) + to_integer(at(full_product, (22208u32 * a)));
      have at(full_product, 22208u32) == 22208u32 by close();
      have at(full_product, a) == at(full_lane_prefix, a) by close();
      have to_integer(at(full_product, (22208u32 * a))) == 22208 * to_integer(at(full_lane_prefix, a)) by {
       rewrite(to_integer(at(full_product, (22208u32 * a))), to_integer(at(full_product, 22208u32) * at(full_product, a)));
       rewrite(to_integer(at(full_product, 22208u32) * at(full_product, a)), to_integer(at(full_product, 22208u32)) * to_integer(at(full_product, a)));
       rewrite(at(full_product, 22208u32), 22208u32);
       rewrite(at(full_product, a), at(full_lane_prefix, a));
       close();
      }
      mark full_seed_add;
      have at(full_seed_add, b) == at(full_lane_prefix, b) by close();
      have to_integer(at(full_seed_add, at(full_product, (22208u32 * a)))) == 22208 * to_integer(at(full_lane_prefix, a)) by close();
      have to_integer(at(full_seed_add, b) + at(full_seed_add, at(full_product, (22208u32 * a)))) == to_integer(at(full_seed_add, b)) + to_integer(at(full_seed_add, at(full_product, (22208u32 * a)))) by close();
      step_until(loop(0).statement(2).entry);
      mark full_reduction_a;
      have at(full_reduction_a, a_vec.0[0]) == at(full_lane_prefix, a_vec.0[0]) by close();
      have at(full_reduction_a, a_vec.0[1]) == at(full_lane_prefix, a_vec.0[1]) by close();
      have at(full_reduction_a, a_vec.0[2]) == at(full_lane_prefix, a_vec.0[2]) by close();
      have at(full_reduction_a, a_vec.0[3]) == at(full_lane_prefix, a_vec.0[3]) by close();
      have to_integer(b) == to_integer(at(full_seed_add, b) + at(full_seed_add, at(full_product, (22208u32 * a)))) by close();
      have to_integer(b) == to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by {
       rewrite(to_integer(b), to_integer(at(full_seed_add, b) + at(full_seed_add, at(full_product, (22208u32 * a)))));
       rewrite(to_integer(at(full_seed_add, b) + at(full_seed_add, at(full_product, (22208u32 * a)))), to_integer(at(full_seed_add, b)) + to_integer(at(full_seed_add, at(full_product, (22208u32 * a)))));
       rewrite(at(full_seed_add, b), at(full_lane_prefix, b));
       rewrite(to_integer(at(full_seed_add, at(full_product, (22208u32 * a)))), 22208 * to_integer(at(full_lane_prefix, a)));
       close();
      }
      step_until(loop(0).statement(3).entry);
      mark full_reduction_b;
      have at(full_reduction_b, b_vec.0[0]) == at(full_lane_prefix, b_vec.0[0]) by close();
      have at(full_reduction_b, b_vec.0[1]) == at(full_lane_prefix, b_vec.0[1]) by close();
      have at(full_reduction_b, b_vec.0[2]) == at(full_lane_prefix, b_vec.0[2]) by close();
      have at(full_reduction_b, b_vec.0[3]) == at(full_lane_prefix, b_vec.0[3]) by close();
      have to_integer(at(full_reduction_b, b)) == to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by close();
      step_until(assignment(b, 2).entry);
      mark full_scalar_mod;
      have to_integer(a) == to_integer(at(full_lane_prefix, a));
      have loop(0).statement(2).call(0).result == 65521u32;
      have to_integer(loop(0).statement(2).call(0).result) == 65521 by { rewrite(loop(0).statement(2).call(0).result, 65521u32); close(); }
      have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[0])), to_integer(loop(0).statement(2).call(0).result)) by close();
      have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[0])), 65521) by {
       rewrite(at(full_lane_prefix, a_vec.0[0]), at(full_reduction_a, a_vec.0[0]));
       rewrite(65521, to_integer(loop(0).statement(2).call(0).result));
       close();
      }
      have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[1])), to_integer(loop(0).statement(2).call(0).result)) by close();
      have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521) by {
       rewrite(at(full_lane_prefix, a_vec.0[1]), at(full_reduction_a, a_vec.0[1]));
       rewrite(65521, to_integer(loop(0).statement(2).call(0).result));
       close();
      }
      have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[2])), to_integer(loop(0).statement(2).call(0).result)) by close();
      have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521) by {
       rewrite(at(full_lane_prefix, a_vec.0[2]), at(full_reduction_a, a_vec.0[2]));
       rewrite(65521, to_integer(loop(0).statement(2).call(0).result));
       close();
      }
      have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[3])), to_integer(loop(0).statement(2).call(0).result)) by close();
      have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521) by {
       rewrite(at(full_lane_prefix, a_vec.0[3]), at(full_reduction_a, a_vec.0[3]));
       rewrite(65521, to_integer(loop(0).statement(2).call(0).result));
       close();
      }
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521) by {
       rewrite(to_integer(a), to_integer(at(full_lane_prefix, a)));
       rewrite(to_integer(a_vec.0[0]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[0])), 65521));
       rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521));
       rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521));
       rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521));
       rewrite(truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521), truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[0])), 65521), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521)), 65521));
       close();
      }
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a)) by {
       rewrite(truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521), truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521));
       rewrite(to_integer(a), to_integer(at(full_lane_prefix, a)));
       close();
      }
      have to_integer(at(full_scalar_mod, b)) == to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by close();
      have loop(0).statement(3).call(0).result == 65521u32;
      have to_integer(loop(0).statement(3).call(0).result) == 65521 by { rewrite(loop(0).statement(3).call(0).result, 65521u32); close(); }
      have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[0])), to_integer(loop(0).statement(3).call(0).result)) by close();
      have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[0])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[0]), at(full_reduction_b, b_vec.0[0])); rewrite(65521, to_integer(loop(0).statement(3).call(0).result)); close(); }
      have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[1])), to_integer(loop(0).statement(3).call(0).result)) by close();
      have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[1])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[1]), at(full_reduction_b, b_vec.0[1])); rewrite(65521, to_integer(loop(0).statement(3).call(0).result)); close(); }
      have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[2])), to_integer(loop(0).statement(3).call(0).result)) by close();
      have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[2])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[2]), at(full_reduction_b, b_vec.0[2])); rewrite(65521, to_integer(loop(0).statement(3).call(0).result)); close(); }
      have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[3])), to_integer(loop(0).statement(3).call(0).result)) by close();
      have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[3])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[3]), at(full_reduction_b, b_vec.0[3])); rewrite(65521, to_integer(loop(0).statement(3).call(0).result)); close(); }
      step();
      have b == at(full_scalar_mod, b) % 65521u32;
      apply(integer::uint32_remainder_to_integer(at(full_scalar_mod, b), 65521u32));
      have to_integer(b) == truncating_remainder(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), 65521) by { rewrite(b, at(full_scalar_mod, b) % 65521u32); rewrite(to_integer(at(full_scalar_mod, b) % 65521u32), truncating_remainder(to_integer(at(full_scalar_mod, b)), to_integer(65521u32))); rewrite(to_integer(at(full_scalar_mod, b)), to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a))); close(); }
      have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == truncating_remainder(adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))), 65521) by {
       rewrite(to_integer(b), truncating_remainder(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), 65521));
       rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521));
       rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521));
       rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521));
       rewrite(to_integer(b_vec.0[0]), truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[0])), 65521));
       rewrite(to_integer(b_vec.0[1]), truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[1])), 65521));
       rewrite(to_integer(b_vec.0[2]), truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[2])), 65521));
       rewrite(to_integer(b_vec.0[3]), truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[3])), 65521));
       close();
      }
      have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521), truncating_remainder(adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))), 65521)); close(); }
      apply(integer::uint32_remainder_less_than_divisor(at(full_scalar_mod, b), 65521u32));
      have b < 65521u32 by { rewrite(b, at(full_scalar_mod, b) % 65521u32); close(); }
      have to_integer(b) <= 65520 by close() using { to_integer(b) < 65521; };
      have loop(0).statement(4).call(0).result == 65521u32;
      have 65521u32 == loop(0).statement(4).call(0).result by close() using { loop(0).statement(4).call(0).result == 65521u32; };
      have loop(0).statement(2).call(0).result == 65521u32;
      have 65521u32 == loop(0).statement(2).call(0).result by close() using { loop(0).statement(2).call(0).result == 65521u32; };
      have a_vec.0[0] < loop(0).statement(2).call(0).result;
      have a_vec.0[0] < 65521u32 by { rewrite(65521u32, loop(0).statement(2).call(0).result); close(); }
      have to_integer(a_vec.0[0]) <= 65520 by close() using { to_integer(a_vec.0[0]) < 65521; };
      have a_vec.0[1] < loop(0).statement(2).call(0).result;
      have a_vec.0[1] < 65521u32 by { rewrite(65521u32, loop(0).statement(2).call(0).result); close(); }
      have to_integer(a_vec.0[1]) <= 65520 by close() using { to_integer(a_vec.0[1]) < 65521; };
      have a_vec.0[2] < loop(0).statement(2).call(0).result;
      have a_vec.0[2] < 65521u32 by { rewrite(65521u32, loop(0).statement(2).call(0).result); close(); }
      have to_integer(a_vec.0[2]) <= 65520 by close() using { to_integer(a_vec.0[2]) < 65521; };
      have a_vec.0[3] < loop(0).statement(2).call(0).result;
      have a_vec.0[3] < 65521u32 by { rewrite(65521u32, loop(0).statement(2).call(0).result); close(); }
      have to_integer(a_vec.0[3]) <= 65520 by close() using { to_integer(a_vec.0[3]) < 65521; };
      have b_vec.0[0] < loop(0).statement(4).call(0).result;
      have b_vec.0[0] < 65521u32 by { rewrite(65521u32, loop(0).statement(4).call(0).result); close(); }
      have to_integer(b_vec.0[0]) <= 65520 by close() using { to_integer(b_vec.0[0]) < 65521; };
      have b_vec.0[1] < loop(0).statement(4).call(0).result;
      have b_vec.0[1] < 65521u32 by { rewrite(65521u32, loop(0).statement(4).call(0).result); close(); }
      have to_integer(b_vec.0[1]) <= 65520 by close() using { to_integer(b_vec.0[1]) < 65521; };
      have b_vec.0[2] < loop(0).statement(4).call(0).result;
      have b_vec.0[2] < 65521u32 by { rewrite(65521u32, loop(0).statement(4).call(0).result); close(); }
      have to_integer(b_vec.0[2]) <= 65520 by close() using { to_integer(b_vec.0[2]) < 65521; };
      have b_vec.0[3] < loop(0).statement(4).call(0).result;
      have b_vec.0[3] < 65521u32 by { rewrite(65521u32, loop(0).statement(4).call(0).result); close(); }
      have to_integer(b_vec.0[3]) <= 65520 by close() using { to_integer(b_vec.0[3]) < 65521; };
      have adler_chunk_bytes(loop(0).iter.len(), 22208u64) < at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by close() using { to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)) - 22208u64); 22208u64 <= at(outer_head, adler_chunk_bytes(loop(0).iter.len(), 22208u64)); };
      mark batch_reduced;
      have truncating_remainder(adler_lane_a(to_integer(at(batch_reduced, a)), to_integer(at(batch_reduced, a_vec.0[0])), to_integer(at(batch_reduced, a_vec.0[1])), to_integer(at(batch_reduced, a_vec.0[2])), to_integer(at(batch_reduced, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(batch_reduced, bytes.as_ptr()), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(at(batch_reduced, a))) by close();
      have truncating_remainder(adler_lane_b(to_integer(at(batch_reduced, b)), to_integer(at(batch_reduced, a_vec.0[1])), to_integer(at(batch_reduced, a_vec.0[2])), to_integer(at(batch_reduced, a_vec.0[3])), to_integer(at(batch_reduced, b_vec.0[0])), to_integer(at(batch_reduced, b_vec.0[1])), to_integer(at(batch_reduced, b_vec.0[2])), to_integer(at(batch_reduced, b_vec.0[3]))), 65521) == adler_spec_b_u64(at(batch_reduced, bytes.as_ptr()), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(at(batch_reduced, a)), old(to_integer((self.b as u32)))) by close();
      have to_integer(at(batch_reduced, a_vec.0[0])) <= 65520 by close() using { to_integer(a_vec.0[0]) <= 65520; };
      have to_integer(at(batch_reduced, a_vec.0[1])) <= 65520 by close() using { to_integer(a_vec.0[1]) <= 65520; };
      have to_integer(at(batch_reduced, a_vec.0[2])) <= 65520 by close() using { to_integer(a_vec.0[2]) <= 65520; };
      have to_integer(at(batch_reduced, a_vec.0[3])) <= 65520 by close() using { to_integer(a_vec.0[3]) <= 65520; };
      have to_integer(at(batch_reduced, b_vec.0[0])) <= 65520 by close() using { to_integer(b_vec.0[0]) <= 65520; };
      have to_integer(at(batch_reduced, b_vec.0[1])) <= 65520 by close() using { to_integer(b_vec.0[1]) <= 65520; };
      have to_integer(at(batch_reduced, b_vec.0[2])) <= 65520 by close() using { to_integer(b_vec.0[2]) <= 65520; };
      have to_integer(at(batch_reduced, b_vec.0[3])) <= 65520 by close() using { to_integer(b_vec.0[3]) <= 65520; };
      step_until(loop.back_edge);
      have a_vec.0[0] == at(batch_reduced, a_vec.0[0]);
      have to_integer(a_vec.0[0]) <= 65520 by { rewrite(a_vec.0[0], at(batch_reduced, a_vec.0[0])); close(); }
      have a_vec.0[1] == at(batch_reduced, a_vec.0[1]);
      have to_integer(a_vec.0[1]) <= 65520 by { rewrite(a_vec.0[1], at(batch_reduced, a_vec.0[1])); close(); }
      have a_vec.0[2] == at(batch_reduced, a_vec.0[2]);
      have to_integer(a_vec.0[2]) <= 65520 by { rewrite(a_vec.0[2], at(batch_reduced, a_vec.0[2])); close(); }
      have a_vec.0[3] == at(batch_reduced, a_vec.0[3]);
      have to_integer(a_vec.0[3]) <= 65520 by { rewrite(a_vec.0[3], at(batch_reduced, a_vec.0[3])); close(); }
      have b_vec.0[0] == at(batch_reduced, b_vec.0[0]);
      have to_integer(b_vec.0[0]) <= 65520 by { rewrite(b_vec.0[0], at(batch_reduced, b_vec.0[0])); close(); }
      have b_vec.0[1] == at(batch_reduced, b_vec.0[1]);
      have to_integer(b_vec.0[1]) <= 65520 by { rewrite(b_vec.0[1], at(batch_reduced, b_vec.0[1])); close(); }
      have b_vec.0[2] == at(batch_reduced, b_vec.0[2]);
      have to_integer(b_vec.0[2]) <= 65520 by { rewrite(b_vec.0[2], at(batch_reduced, b_vec.0[2])); close(); }
      have b_vec.0[3] == at(batch_reduced, b_vec.0[3]);
      have to_integer(b_vec.0[3]) <= 65520 by { rewrite(b_vec.0[3], at(batch_reduced, b_vec.0[3])); close(); }
      have bytes.as_ptr() == old(bytes.as_ptr()) by close();
      have bytes.len() == old(bytes.len() - bytes.len() % 4u64) by close();
      have a <= 65520u32 by close();
      have b <= 65520u32 by close();
      have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64 by close();
      have remainder_chunk.len() == (bytes.len()) % 22208u64 by close();
      have remainder.len() == old(bytes.len() % 4u64) by close();
      have to_integer(a_vec.0[0]) <= 65520 by close();
      have to_integer(a_vec.0[1]) <= 65520 by close();
      have to_integer(a_vec.0[2]) <= 65520 by close();
      have to_integer(a_vec.0[3]) <= 65520 by close();
      have to_integer(b_vec.0[0]) <= 65520 by close();
      have to_integer(b_vec.0[1]) <= 65520 by close();
      have to_integer(b_vec.0[2]) <= 65520 by close();
      have to_integer(b_vec.0[3]) <= 65520 by close();
      have (bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))) == bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by close();
      have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) } by close();
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a)) by {
       rewrite(a, at(batch_reduced, a));
       rewrite(a_vec.0[0], at(batch_reduced, a_vec.0[0]));
       rewrite(a_vec.0[1], at(batch_reduced, a_vec.0[1]));
       rewrite(a_vec.0[2], at(batch_reduced, a_vec.0[2]));
       rewrite(a_vec.0[3], at(batch_reduced, a_vec.0[3]));
       close();
      }
      have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32)))) by close();
      // The outer invariants at the back edge, one batch further on.
      have loop(0).iter.len() == at(outer_head, loop(0).iter.len()) - 1u64;
      have to_integer(loop(0).iter.len()) + (iterations + 1) == to_integer((bytes.len()) / 22208u64) by close() using { loop(0).iter.len() == at(outer_head, loop(0).iter.len()) - 1u64; 0u64 < at(outer_head, loop(0).iter.len()); to_integer(at(outer_head, loop(0).iter.len())) + iterations == to_integer((bytes.len()) / 22208u64); };
      have iterations + 1 == (to_integer((bytes.len()) / 22208u64) - to_integer(loop(0).iter.len())) by close() using { to_integer(loop(0).iter.len()) + (iterations + 1) == to_integer((bytes.len()) / 22208u64); };
      have loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) by close();
      have loop(0).iter.len() <= (bytes.len()) / 22208u64;
       // Every invariant at the back edge.
       have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len());
       have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
       have bytes.as_ptr() == old(bytes.as_ptr());
       have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
       have bytes.len() == old(bytes.len() - bytes.len() % 4u64);
       have a <= 65520u32;
       have b <= 65520u32;
       have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
       have remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
       have loop(0).iter.chunk_size == 22208u64;
       have remainder_chunk.len() == (bytes.len()) % 22208u64;
       have remainder.len() == old(bytes.len() % 4u64);
       have to_integer(a_vec.0[0]) <= 65520;
       have to_integer(a_vec.0[1]) <= 65520;
       have to_integer(a_vec.0[2]) <= 65520;
       have to_integer(a_vec.0[3]) <= 65520;
       have to_integer(b_vec.0[0]) <= 65520;
       have to_integer(b_vec.0[1]) <= 65520;
       have to_integer(b_vec.0[2]) <= 65520;
       have to_integer(b_vec.0[3]) <= 65520;
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a));
       have 0 <= old(to_integer((self.b as u32)));
       have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32))));
       have loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       have to_integer(loop(0).iter.len()) + (iterations + 1) == to_integer((bytes.len()) / 22208u64);
       // The ranking members: the measure is read at the pass entry, before the header ran.
       have at(outer_head, loop(0).iter.len()) == at(outer_pass, loop(0).iter.len());
       have loop(0).iter.len() < at(outer_head, loop(0).iter.len()) by close() using { loop(0).iter.len() == at(outer_head, loop(0).iter.len()) - 1u64; 0u64 < at(outer_head, loop(0).iter.len()); };
       have loop(0).iter.len() < at(outer_pass, loop(0).iter.len()) by close() using { loop(0).iter.len() < at(outer_head, loop(0).iter.len()); at(outer_head, loop(0).iter.len()) == at(outer_pass, loop(0).iter.len()); };
      } else {
       // No chunk is left: the header test fails and the loop leaves by `break`.
       step();
       have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len());
       have to_integer(adler_chunk_bytes(loop(0).iter.len(), 22208u64)) <= to_integer(((bytes.len()) - (bytes.len()) % 22208u64));
       have bytes.as_ptr() == old(bytes.as_ptr());
       have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
       have bytes.len() == old(bytes.len() - bytes.len() % 4u64);
       have a <= 65520u32;
       have b <= 65520u32;
       have adler_chunk_bytes(loop(0).iter.len(), 22208u64) % 22208u64 == 0u64;
       have remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
       have loop(0).iter.chunk_size == 22208u64;
       have remainder_chunk.len() == (bytes.len()) % 22208u64;
       have remainder.len() == old(bytes.len() % 4u64);
       have to_integer(a_vec.0[0]) <= 65520;
       have to_integer(a_vec.0[1]) <= 65520;
       have to_integer(a_vec.0[2]) <= 65520;
       have to_integer(a_vec.0[3]) <= 65520;
       have to_integer(b_vec.0[0]) <= 65520;
       have to_integer(b_vec.0[1]) <= 65520;
       have to_integer(b_vec.0[2]) <= 65520;
       have to_integer(b_vec.0[3]) <= 65520;
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a));
       have 0 <= old(to_integer((self.b as u32)));
       have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64), to_integer(a), old(to_integer((self.b as u32))));
       have loop(0).iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64));
       have to_integer(loop(0).iter.len()) + iterations == to_integer((bytes.len()) / 22208u64);
       step();
      }
     }
     }
     have loop(0).iter.len() == 0u64;
     apply(adler_chunk_bytes_none(22208u64));
     have adler_chunk_bytes(loop(0).iter.len(), 22208u64) == 0u64 by { rewrite(loop(0).iter.len(), 0u64); close(); }
     have adler_chunk_bytes(loop(0).iter.len(), 22208u64) < 22208u64 by close() using { adler_chunk_bytes(loop(0).iter.len(), 22208u64) == 0u64; };
     apply(adler_outer_exhausted_remaining_u64(adler_chunk_bytes(loop(0).iter.len(), 22208u64)));
     have to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64)) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) by { rewrite(adler_chunk_bytes(loop(0).iter.len(), 22208u64), 0u64); close(); }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64), to_integer(a)) by { rewrite(to_integer(((bytes.len()) - (bytes.len()) % 22208u64)), to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); close(); }
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), ((bytes.len()) - (bytes.len()) % 22208u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(to_integer(((bytes.len()) - (bytes.len()) % 22208u64)), to_integer(((bytes.len()) - (bytes.len()) % 22208u64) - adler_chunk_bytes(loop(0).iter.len(), 22208u64))); close(); }
     apply(adler_outer_remainder_bounds_u64(bytes.len()));
     apply(adler_outer_remainder_signed_bound_u64(bytes.len()));
     apply(adler_outer_remainder_signed_divisible_u64(bytes.len()));
     have remainder_chunk.len() <= 22204u64 by { rewrite(remainder_chunk.len(), (bytes.len()) % 22208u64); close(); }
     have remainder_chunk.len() <= 2147483647u64 by close() using { remainder_chunk.len() <= 22204u64; };
     have ((remainder_chunk.len() as u32) as i32) == ((((bytes.len()) % 22208u64) as u32) as i32) by { rewrite(remainder_chunk.len(), (bytes.len()) % 22208u64); close(); }
     have 0 <= ((remainder_chunk.len() as u32) as i32) by { rewrite(((remainder_chunk.len() as u32) as i32), ((((bytes.len()) % 22208u64) as u32) as i32)); close(); }
     have remainder_chunk.len() % 4u64 == 0u64 by { rewrite(remainder_chunk.len(), (bytes.len()) % 22208u64); close(); }
     mark remainder_ctor;
     step_until(loop(2).entry);
     // The remainder iterator covers the saved remainder in four-byte chunks.
     have loop(2).iter.v == remainder_chunk.as_ptr();
     have loop(2).iter.chunk_size == 4u64;
     have loop(2).iter.len() == remainder_chunk.len() / 4u64 by close();
     apply(adler_chunk_bytes_whole_4(remainder_chunk.len()));
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) == remainder_chunk.len() by { rewrite(loop(2).iter.len(), remainder_chunk.len() / 4u64); close(); }
     have loop(2).iter.len() <= remainder_chunk.len() / 4u64;
     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) == ((remainder_chunk.len() as u32) as i32) by { rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), remainder_chunk.len()); close(); }
     have ((remainder_chunk.len() as u32) as i32) == ((((bytes.len()) % 22208u64) as u32) as i32) by { rewrite(remainder_chunk.len(), (bytes.len()) % 22208u64); close(); }
     have 0 <= ((remainder_chunk.len() as u32) as i32) by { rewrite(((remainder_chunk.len() as u32) as i32), ((((bytes.len()) % 22208u64) as u32) as i32)); close(); }
     have ((remainder_chunk.len() as u32) as i32) <= 22204 by { rewrite(((remainder_chunk.len() as u32) as i32), ((((bytes.len()) % 22208u64) as u32) as i32)); close(); }
     have (((remainder_chunk.len() as u32) as i32)) % 4 == 0 by { rewrite(((remainder_chunk.len() as u32) as i32), ((((bytes.len()) % 22208u64) as u32) as i32)); close(); }
     apply(adler_lane_initial_ceiling());
     apply(adler_lane_iterator_initial(((remainder_chunk.len() as u32) as i32)));
     have adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == 0 by { rewrite(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32), ((remainder_chunk.len() as u32) as i32)); close(); }
     have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[0]) <= 65520; }; }
     have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[0]) <= 65520; }; }
     have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[1]) <= 65520; }; }
     have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[1]) <= 65520; }; }
     have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[2]) <= 65520; }; }
     have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[2]) <= 65520; }; }
     have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[3]) <= 65520; }; }
     have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[3]) <= 65520; }; }
     have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) by { rewrite(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32), ((remainder_chunk.len() as u32) as i32)); close(); }
     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32) by { rewrite(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32), ((remainder_chunk.len() as u32) as i32)); close() using {}; }
     have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32) by close();
     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by { rewrite(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32), ((remainder_chunk.len() as u32) as i32)); close(); }
     have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32));
     have bytes.len() == old(bytes.len() - bytes.len() % 4u64) by close();
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64 by close() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) == remainder_chunk.len(); remainder_chunk.len() <= 22204u64; };
     apply(adler_bounded_count(remainder_chunk.len()));
     have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk by { rewrite(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32), ((remainder_chunk.len() as u32) as i32)); close(); }
     have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by {
      apply(adler_uint64_self_subtract(remainder_chunk.len())); rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), remainder_chunk.len()); rewrite(to_integer(remainder_chunk.len() - remainder_chunk.len()), to_integer(0u64)); close() using { (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk; };
     }
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk.len() by { rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), remainder_chunk.len()); close(); }
     have to_integer((bytes.len())) <= to_integer(bytes.len()) by close() using { bytes.len() % 4u64 <= bytes.len(); };
     have to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len())) by close();
     have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer((bytes.len())) by close() using { to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len())); bytes.len() % 4u64 <= bytes.len(); };
     have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer(bytes.len()) by close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) <= to_integer((bytes.len())); to_integer((bytes.len())) <= to_integer(bytes.len()); to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len())); bytes.len() % 4u64 <= bytes.len(); };
     have to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) by { rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), remainder_chunk.len()); rewrite(remainder_chunk.len(), (bytes.len()) % 22208u64); close(); }
     have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by { rewrite(to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len()) - (bytes.len()) % 22208u64))); close() using { (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk; remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64); }; }
     have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len())) by { rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), remainder_chunk.len()); rewrite(remainder_chunk.len(), (bytes.len()) % 22208u64); close(); }
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
     apply(adler_canonical_lane_b_floor(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])));
     apply(adler_empty_remainder_position(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
     have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))), 0); have to_integer(b) + 0 * to_integer(a) == to_integer(b) by close() using {}; rewrite(to_integer(b) + 0 * to_integer(a), to_integer(b)); close(); }
     // The remainder continues the uint64 running prefix at its cursor.
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a)) by { rewrite(to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len()) - (bytes.len()) % 22208u64))); close(); }
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len()) - (bytes.len()) % 22208u64))); rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))), 0); have to_integer(b) + 0 * to_integer(a) == to_integer(b) by close() using {}; rewrite(to_integer(b) + 0 * to_integer(a), to_integer(b)); close(); }
     have defined(((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32));
     loop {
      decreases loop(2).iter.len();
      invariant loop(2).iter.chunk_size == 4u64;
      invariant loop(2).iter.v.len() == adler_chunk_bytes(loop(2).iter.len(), 4u64);
     invariant adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64;
      owns a_vec.0[0..4];
      owns b_vec.0[0..4];
      views *bytes;

      invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a));
      invariant 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
      invariant truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
      invariant adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk.len();
      invariant remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
      invariant (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64));
      invariant to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len()));
      invariant to_integer((bytes.len())) <= to_integer(bytes.len());
      invariant bytes.len() % 4u64 <= bytes.len();
      invariant bytes.as_ptr() == old(bytes.as_ptr());
      invariant bytes.len() == old(bytes.len() - bytes.len() % 4u64);
      invariant a <= 65520u32;
      invariant b <= 65520u32;
      invariant 0 <= ((remainder_chunk.len() as u32) as i32);
      invariant ((remainder_chunk.len() as u32) as i32) <= 22204;
      invariant ((remainder_chunk.len() as u32) as i32) % 4 == 0;
      invariant 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32);
      invariant ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
      invariant to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
      invariant remainder_chunk.len() == (bytes.len()) % 22208u64;
      invariant remainder.len() == old(bytes.len() % 4u64);
      invariant loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64));
      invariant to_integer(loop(2).iter.len()) + iterations == to_integer(remainder_chunk.len() / 4u64);
      invariant remainder_chunk.len() % 4u64 == 0u64;
      invariant remainder_chunk.len() <= 22204u64;
      initialize by {
       have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64;
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a));
       have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
       have 0 <= old(to_integer((self.b as u32)));
       have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
       have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk.len();
       have remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
       have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by { close(); close(); }
       have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len()));
       have to_integer((bytes.len())) <= to_integer(bytes.len());
       have bytes.len() % 4u64 <= bytes.len();
       have bytes.as_ptr() == old(bytes.as_ptr());
       have bytes.len() == old(bytes.len() - bytes.len() % 4u64);
       have a <= 65520u32;
       have b <= 65520u32;
       have 0 <= ((remainder_chunk.len() as u32) as i32);
       have ((remainder_chunk.len() as u32) as i32) <= 22204;
       have ((remainder_chunk.len() as u32) as i32) % 4 == 0;
       have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32);
       have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
       have remainder_chunk.len() == (bytes.len()) % 22208u64;
       have remainder.len() == old(bytes.len() % 4u64);
       have loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by close();
       have to_integer(loop(2).iter.len()) + iterations == to_integer(remainder_chunk.len() / 4u64);
       have remainder_chunk.len() % 4u64 == 0u64;
       have remainder_chunk.len() <= 22204u64;
      }
      maintain by {
       mark remainder_pass;
       if loop(2).iter.chunk_size <= loop(2).iter.v.len() {
        have loop(2).iter.chunk_size == 4u64;
        have 4u64 <= loop(2).iter.v.len();
        have to_integer(4u64) <= to_integer(loop(2).iter.v.len());
        apply(integer::positive_divisor_quotient_lower(to_integer(loop(2).iter.v.len()), to_integer(4u64), 1));
        apply(integer::uint64_divide_to_integer(loop(2).iter.v.len(), 4u64));
        have 0u64 < loop(2).iter.len() by close();
        have loop(2).iter.len() <= remainder_chunk.len() / 4u64 by close() using { to_integer(loop(2).iter.len()) + iterations == to_integer(remainder_chunk.len() / 4u64); 0 <= iterations; };
        apply(integer::uint64_subtract_to_integer(remainder_chunk.len() / 4u64, loop(2).iter.len()));
        have to_integer((remainder_chunk.len() / 4u64 - loop(2).iter.len())) == iterations by close() using { to_integer((remainder_chunk.len() / 4u64 - loop(2).iter.len())) == to_integer(remainder_chunk.len() / 4u64) - to_integer(loop(2).iter.len()); to_integer(loop(2).iter.len()) + iterations == to_integer(remainder_chunk.len() / 4u64); };
        have loop(2).iter.chunk_size == 4u64;
        apply(adler_chunk_bytes_next_4(loop(2).iter.len(), remainder_chunk.len()));
        apply(adler_chunk_bytes_offset_whole_4(loop(2).iter.len(), remainder_chunk.len()));
        have 4u64 <= adler_chunk_bytes(loop(2).iter.len(), 4u64);
        have to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) + 4u64) <= to_integer(remainder_chunk.len()) by close() using {
         adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk.len(); 4u64 <= adler_chunk_bytes(loop(2).iter.len(), 4u64);
        };
        have 4 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) by {
         have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 2147483647u64 by close() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64; };
         apply(adler_bounded_count_lower(adler_chunk_bytes(loop(2).iter.len(), 4u64), 4)); close();
        }
        have 4u64 <= adler_chunk_bytes(loop(2).iter.len(), 4u64);
        have to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len())) by close() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len())); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer(bytes.len()) by close() using { to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len())); to_integer((bytes.len())) <= to_integer(bytes.len()); to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len())); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(4u64) <= to_integer(bytes.len() - ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by close() using { 4u64 <= adler_chunk_bytes(loop(2).iter.len(), 4u64); to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len())); to_integer((bytes.len())) <= to_integer(bytes.len()); bytes.len() % 4u64 <= bytes.len(); };
        // The first fact about the chunk's pointer is its offset from `bytes`: the helper call
        // below reads the chunk through the input's view, and the view is found by that fact.
        have loop(2).iter.v == bytes.as_ptr() + ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by {
         have loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() / 4u64 - loop(2).iter.len()) * 4u64 by close();
         have loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by {
          rewrite(to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer((remainder_chunk.len() / 4u64 - loop(2).iter.len()) * 4u64));
          close();
         }
         apply(integer::uint64_subtract_to_integer(remainder_chunk.len(), adler_chunk_bytes(loop(2).iter.len(), 4u64)));
         apply(integer::uint64_subtract_to_integer((bytes.len()), adler_chunk_bytes(loop(2).iter.len(), 4u64)));
         have to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len())) by close();
         apply(integer::uint64_subtract_to_integer((bytes.len()), (bytes.len()) % 22208u64));
         have to_integer(remainder_chunk.len()) == to_integer((bytes.len()) % 22208u64) by close() using { remainder_chunk.len() == (bytes.len()) % 22208u64; };
         have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by close() using { to_integer(remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(remainder_chunk.len()) - to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer((bytes.len())) - to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer((bytes.len()) - (bytes.len()) % 22208u64) == to_integer((bytes.len())) - to_integer((bytes.len()) % 22208u64); to_integer(remainder_chunk.len()) == to_integer((bytes.len()) % 22208u64); };
         have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= 18446744073709551615 by close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer(bytes.len()); };
         apply(integer::uint64_add_to_integer(((bytes.len()) - (bytes.len()) % 22208u64), (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))));
         have remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by { rewrite(remainder_chunk.as_ptr(), bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64)); close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= 18446744073709551615; to_integer(((bytes.len()) - (bytes.len()) % 22208u64) + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))); }; }
         have to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64) + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64) + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
         rewrite(to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len()) - (bytes.len()) % 22208u64) + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))));
         close() using { loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)); remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == bytes.as_ptr() + (((bytes.len()) - (bytes.len()) % 22208u64) + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
        }
        apply(integer::uint64_subtract_to_integer(remainder_chunk.len(), adler_chunk_bytes(loop(2).iter.len(), 4u64)));
        apply(integer::uint64_subtract_to_integer((bytes.len()), adler_chunk_bytes(loop(2).iter.len(), 4u64)));
        have to_integer((bytes.len()) % 22208u64) <= to_integer((bytes.len())) by close();
        apply(integer::uint64_subtract_to_integer((bytes.len()), (bytes.len()) % 22208u64));
        have to_integer(remainder_chunk.len()) == to_integer((bytes.len()) % 22208u64) by close() using { remainder_chunk.len() == (bytes.len()) % 22208u64; };
        have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by close() using { to_integer(remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(remainder_chunk.len()) - to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer((bytes.len())) - to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer((bytes.len()) - (bytes.len()) % 22208u64) == to_integer((bytes.len())) - to_integer((bytes.len()) % 22208u64); to_integer(remainder_chunk.len()) == to_integer((bytes.len()) % 22208u64); };
        have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= 18446744073709551615 by close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer(bytes.len()); };
        apply(integer::uint64_add_to_integer(((bytes.len()) - (bytes.len()) % 22208u64), (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))));
        have to_integer(((bytes.len()) - (bytes.len()) % 22208u64) + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) by close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64) + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
        apply(integer::uint64_subtract_to_integer(bytes.len(), ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))));
        have to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()) by close() using { to_integer(4u64) <= to_integer(bytes.len() - ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(bytes.len() - ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(bytes.len()) - to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
        have to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) < to_integer(bytes.len()) by close() using { to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        have to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(3u64) <= 18446744073709551615 by close() using { to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        apply(integer::uint64_add_to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64)), 3u64));
        have to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) + 3u64) < to_integer(bytes.len()) by close() using { to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) + 3u64) == to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(3u64); to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        have to_integer(((bytes.len()) - (bytes.len()) % 22208u64) + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) < to_integer(bytes.len()) by close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64) + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) < to_integer(bytes.len()); };
        have to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 3 < to_integer(bytes.len()) by close() using { to_integer(((bytes.len()) - (bytes.len()) % 22208u64)) + to_integer((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) + to_integer(4u64) <= to_integer(bytes.len()); };
        // The same chunk starts `remainder_chunk.len() - remaining` bytes into the remainder, where the old cursor stood.
        have loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by {
         have loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() / 4u64 - loop(2).iter.len()) * 4u64 by close();
         rewrite(to_integer(remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)), to_integer((remainder_chunk.len() / 4u64 - loop(2).iter.len()) * 4u64));
         close();
        }
        have remainder_chunk.len() <= 22208u64 by close() using { remainder_chunk.len() <= 22204u64; };
        have remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64 by close() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk.len(); remainder_chunk.len() <= 22208u64; };
        apply(adler_count_byte_pointer(remainder_chunk, remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)));
        apply(adler_count_step(remainder_chunk.len(), adler_chunk_bytes(loop(2).iter.len(), 4u64)));
        have loop(2).iter.v == (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by {
         rewrite(to_integer(((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), to_integer((((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) as uint32) as int32)));
         close() using { loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)); remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == remainder_chunk.as_ptr() + (((remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64)) as uint32) as int32); };
        }
        mark lane_head;
        have at(lane_head, loop(2).iter.v) == at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have at(lane_head, loop(2).iter.chunk_size) == 4u64;
        have 0u64 < at(lane_head, loop(2).iter.len());
        have to_integer(adler_chunk_bytes(at(lane_head, loop(2).iter.len()) - 1u64, 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64);
        have to_integer(at(lane_head, loop(2).iter.len())) + iterations == to_integer(remainder_chunk.len() / 4u64);
        have at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) % 4 == 0;
        have at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32);
        have 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32));
        have 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32));
        have ((remainder_chunk.len() as u32) as i32) <= 22208 by close() using { ((remainder_chunk.len() as u32) as i32) <= 22204; };

        have 0 <= to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { 0 <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); };
        have to_integer((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) + 4) <= to_integer(((remainder_chunk.len() as u32) as i32)) by close() using { 0 <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); };
        have to_integer((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) <= 22204 by close() using { 0 <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); };
        step_until(loop(2).statement(0).entry);
        have byte_vec.as_ptr() == at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have byte_vec.len() == 4u64;
        have loop(2).iter.v == at(lane_head, loop(2).iter.v) + 4u64 by close();
        have 4u64 <= at(lane_head, loop(2).iter.v.len());
        apply(integer::uint64_subtract_to_integer(at(lane_head, loop(2).iter.v.len()), 4u64));
        have loop(2).iter.v.len() == at(lane_head, loop(2).iter.v.len()) - 4u64 by close();
        have loop(2).iter.len() == at(lane_head, loop(2).iter.len()) - 1u64;
        have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64) by { rewrite(loop(2).iter.len(), at(lane_head, loop(2).iter.len()) - 1u64); close(); }
        have 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64));
        have at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= 22208u64;
        apply(integer::uint64_subtract_to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)), 4u64));
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) == at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64 by close() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) - to_integer(4u64); };
        apply(adler_count_lane_step(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))));
        have to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4);
        have to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; };
        have 0 <= to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) by { rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))))); close(); }
        have to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) <= 22204 by { rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))))); close(); }
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); };
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; };
        have byte_vec.as_ptr() == remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) by {
         rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))));
         close() using { byte_vec.as_ptr() == at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) == remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); };
        }
        apply(adler_current_window(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));



        mark byte_view;
        have byte_vec.as_ptr() == at(byte_view, byte_vec.as_ptr());
        have byte_vec.as_ptr() == at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) == bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) by close();
        have byte_vec.as_ptr() == bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) by close() using { byte_vec.as_ptr() == byte_vec.as_ptr(); byte_vec.as_ptr() == at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) == bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
        have byte_vec.as_ptr() == bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) by close() using { byte_vec.as_ptr() == byte_vec.as_ptr(); byte_vec.as_ptr() == bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))); };

        have to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer((bytes.len())) by close() using { to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len())); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer(bytes.len()) by close() using { to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer((bytes.len())); to_integer((bytes.len())) <= to_integer(bytes.len()); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len())); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(4u64) <= to_integer(bytes.len() - ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) by close() using { 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len())); to_integer((bytes.len())) <= to_integer(bytes.len()); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64) by close() using { 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len())); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) + 4 <= 18446744073709551615 by close() using { to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64); };
        mark remainder_constructor;
        step_until(loop(2).statement(1).entry);
        mark vector_a;
        // Use the checked constructor's exact call-entry byte observations.
        have at(remainder_constructor, byte_vec.as_ptr()) == bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) by close() using { byte_vec.as_ptr() == bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))); };
        have to_integer(at(vector_a, val.0[0])) == at(remainder_constructor, to_integer((byte_vec[0] as i32))) by close() using { to_integer(val.0[0]) == at(remainder_constructor, to_integer((byte_vec[0] as i32))); };
        have at(remainder_constructor, (byte_vec[0] as i32)) == at(remainder_constructor, ((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32)) by {
         rewrite(at(remainder_constructor, byte_vec.as_ptr()), bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))); close();
        }
        have to_integer(at(vector_a, val.0[0])) == at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[0])), at(remainder_constructor, to_integer((byte_vec[0] as i32))));
         rewrite(at(remainder_constructor, (byte_vec[0] as i32)), at(remainder_constructor, ((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32)));
         close();
        }
        have at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32))) == at(vector_a, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32))) by close();
        have to_integer(at(vector_a, val.0[0])) == at(vector_a, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[0])), at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[0] as i32)))); close();
        }
        have to_integer(at(vector_a, val.0[1])) == at(remainder_constructor, to_integer((byte_vec[1] as i32))) by close() using { to_integer(val.0[1]) == at(remainder_constructor, to_integer((byte_vec[1] as i32))); };
        have at(remainder_constructor, (byte_vec[1] as i32)) == at(remainder_constructor, ((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32)) by {
         rewrite(at(remainder_constructor, byte_vec.as_ptr()), bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))); close();
        }
        have to_integer(at(vector_a, val.0[1])) == at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[1])), at(remainder_constructor, to_integer((byte_vec[1] as i32))));
         rewrite(at(remainder_constructor, (byte_vec[1] as i32)), at(remainder_constructor, ((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32)));
         close();
        }
        have at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32))) == at(vector_a, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32))) by close();
        have to_integer(at(vector_a, val.0[1])) == at(vector_a, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[1])), at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[1] as i32)))); close();
        }
        have to_integer(at(vector_a, val.0[2])) == at(remainder_constructor, to_integer((byte_vec[2] as i32))) by close() using { to_integer(val.0[2]) == at(remainder_constructor, to_integer((byte_vec[2] as i32))); };
        have at(remainder_constructor, (byte_vec[2] as i32)) == at(remainder_constructor, ((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32)) by {
         rewrite(at(remainder_constructor, byte_vec.as_ptr()), bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))); close();
        }
        have to_integer(at(vector_a, val.0[2])) == at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[2])), at(remainder_constructor, to_integer((byte_vec[2] as i32))));
         rewrite(at(remainder_constructor, (byte_vec[2] as i32)), at(remainder_constructor, ((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32)));
         close();
        }
        have at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32))) == at(vector_a, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32))) by close();
        have to_integer(at(vector_a, val.0[2])) == at(vector_a, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[2])), at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[2] as i32)))); close();
        }
        have to_integer(at(vector_a, val.0[3])) == at(remainder_constructor, to_integer((byte_vec[3] as i32))) by close() using { to_integer(val.0[3]) == at(remainder_constructor, to_integer((byte_vec[3] as i32))); };
        have at(remainder_constructor, (byte_vec[3] as i32)) == at(remainder_constructor, ((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32)) by {
         rewrite(at(remainder_constructor, byte_vec.as_ptr()), bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))); close();
        }
        have to_integer(at(vector_a, val.0[3])) == at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[3])), at(remainder_constructor, to_integer((byte_vec[3] as i32))));
         rewrite(at(remainder_constructor, (byte_vec[3] as i32)), at(remainder_constructor, ((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32)));
         close();
        }
        have at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32))) == at(vector_a, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32))) by close();
        have to_integer(at(vector_a, val.0[3])) == at(vector_a, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32))) by {
         rewrite(to_integer(at(vector_a, val.0[3])), at(remainder_constructor, to_integer(((bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))))[3] as i32)))); close();
        }
        have 0 <= to_integer(at(vector_a, a_vec.0[0]));
        have 0 <= to_integer(at(vector_a, b_vec.0[0]));
        have to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, val.0[0]));
        have to_integer(at(vector_a, val.0[0])) <= 255;
        apply(adler_lane_iterator_add_contracts(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, val.0[0])));
        apply(adler_lane_iterator_native_preservation(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, val.0[0])));
        have 0 <= to_integer(at(vector_a, a_vec.0[1]));
        have 0 <= to_integer(at(vector_a, b_vec.0[1]));
        have to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, val.0[1]));
        have to_integer(at(vector_a, val.0[1])) <= 255;
        apply(adler_lane_iterator_add_contracts(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, val.0[1])));
        apply(adler_lane_iterator_native_preservation(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, val.0[1])));
        have 0 <= to_integer(at(vector_a, a_vec.0[2]));
        have 0 <= to_integer(at(vector_a, b_vec.0[2]));
        have to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, val.0[2]));
        have to_integer(at(vector_a, val.0[2])) <= 255;
        apply(adler_lane_iterator_add_contracts(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, val.0[2])));
        apply(adler_lane_iterator_native_preservation(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, val.0[2])));
        have 0 <= to_integer(at(vector_a, a_vec.0[3]));
        have 0 <= to_integer(at(vector_a, b_vec.0[3]));
        have to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))));
        have 0 <= to_integer(at(vector_a, val.0[3]));
        have to_integer(at(vector_a, val.0[3])) <= 255;
        apply(adler_lane_iterator_add_contracts(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[3])));
        apply(adler_lane_iterator_native_preservation(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[3])));
        have to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; };
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a_u64(at(vector_a, bytes.as_ptr()), ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(a)) by { close(); }
        have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) by { have to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); }; rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); close(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[0]), at(vector_a, val.0[0])));
        have to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0])), to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))); close(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[1]), at(vector_a, val.0[1])));
        have to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))); close(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[2]), at(vector_a, val.0[2])));
        have to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))); close(); }
        apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[3]), at(vector_a, val.0[3])));
        have to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3])), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))); close(); }
        apply(adler_native_deferred_b_step((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[0]), at(vector_a, val.0[1]), at(vector_a, val.0[2]), at(vector_a, val.0[3])));
        apply(adler_nonnegative_deferred_b_step((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[0]), at(vector_a, val.0[1]), at(vector_a, val.0[2]), at(vector_a, val.0[3])));
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b_u64(at(vector_a, bytes.as_ptr()), ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(at(vector_a, a)), old(to_integer((self.b as u32)))) by { have to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)) == to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); }; rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)), to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); close(); }
        apply(adler_native_deferred_b_prefix_step_u64(at(vector_a, bytes.as_ptr()), ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4), to_integer(a), old(to_integer((self.b as u32))), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[0]), at(vector_a, val.0[1]), at(vector_a, val.0[2]), at(vector_a, val.0[3])));
        apply(adler_native_four_lane_a_prefix_step_u64(at(vector_a, bytes.as_ptr()), ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(a), to_integer(a), at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, val.0[0]), at(vector_a, val.0[1]), at(vector_a, val.0[2]), at(vector_a, val.0[3])));
        step_until(loop(2).statement(2).entry);
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]));
        have b_vec.0[0] == at(vector_a, b_vec.0[0]);
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])) by close() using { b_vec.0[0] == at(vector_a, b_vec.0[0]); };
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) by close() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])); };
        have to_integer(b_vec.0[0]) + to_integer(a_vec.0[0]) <= 4294967295 by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])); to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])); to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) <= 4294967295; };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]));
        have b_vec.0[1] == at(vector_a, b_vec.0[1]);
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])) by close() using { b_vec.0[1] == at(vector_a, b_vec.0[1]); };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); };
        have to_integer(b_vec.0[1]) + to_integer(a_vec.0[1]) <= 4294967295 by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) <= 4294967295; };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]));
        have b_vec.0[2] == at(vector_a, b_vec.0[2]);
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])) by close() using { b_vec.0[2] == at(vector_a, b_vec.0[2]); };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); };
        have to_integer(b_vec.0[2]) + to_integer(a_vec.0[2]) <= 4294967295 by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) <= 4294967295; };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]));
        have b_vec.0[3] == at(vector_a, b_vec.0[3]);
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])) by close() using { b_vec.0[3] == at(vector_a, b_vec.0[3]); };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); };
        have to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]) <= 4294967295 by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) <= 4294967295; };
        mark vector_b;
        step_until(loop.back_edge);
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]));
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])));
        have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) by close() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))) by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]));
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))) by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]));
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))) by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]));
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); };
        have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))) by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))); };
        have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); };
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); };
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); };
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; };
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32) by close();
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by { rewrite(to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)), to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4)); close() using { at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) % 4 == 0; 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; }; }
        have to_integer((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) + 4) == to_integer(((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; };
        have 0 <= to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; };
        have to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) <= 22200 by close() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; };
        have to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) <= 22204 by close() using { to_integer(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) <= 22200; };
        have 0 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) by close() using { 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); };
        have defined(((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));


        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) < at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; };
        have bytes.as_ptr() == old(bytes.as_ptr()) by close();
        have bytes.len() == old(bytes.len() - bytes.len() % 4u64) by close();
        have a <= 65520u32 by close();
        have b <= 65520u32 by close();
        have 0 <= ((remainder_chunk.len() as u32) as i32) by close();
        have ((remainder_chunk.len() as u32) as i32) <= 22204 by close();
        have ((remainder_chunk.len() as u32) as i32) % 4 == 0 by close();
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32) by close();
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0 by close();

        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close();
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) by close();

        have remainder_chunk.len() == (bytes.len()) % 22208u64 by close();
        have remainder.len() == old(bytes.len() % 4u64) by close();
        have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64);
        have 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) by close();
        have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len())) by close() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len())); bytes.len() % 4u64 <= bytes.len(); };
        have to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64) by close() using { 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len())); bytes.len() % 4u64 <= bytes.len(); };
        // The cursor term advanced by four bytes with the count.
        apply(adler_bounded_pointer_association(remainder_chunk, (((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))));
        have at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) == remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) + 4 by { rewrite(at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))), remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); rewrite((remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))) + 4, remainder_chunk.as_ptr() + ((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) + 4)); rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) + 4), to_integer(((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); close() using {}; }
        have to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615 by close() using { to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) <= to_integer(18446744073709551611u64); };
        apply(integer::uint64_add_to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))), 4u64));
        have byte_vec.as_ptr() + 4 == bytes.as_ptr() + (((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64) by { rewrite(byte_vec.as_ptr(), bytes.as_ptr() + ((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))); close() using { to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) + to_integer(4u64) <= 18446744073709551615; to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64) == to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)))) + to_integer(4u64); }; }
        have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == byte_vec.as_ptr() + 4 by { rewrite(byte_vec.as_ptr(), at(lane_head, (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))))); close(); }
        have to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))) == to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64) by close() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) <= to_integer((bytes.len())); bytes.len() % 4u64 <= bytes.len(); };
        have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) by { rewrite(to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64)); close() using { (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == byte_vec.as_ptr() + 4; byte_vec.as_ptr() + 4 == bytes.as_ptr() + (((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64); }; }
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64 by close() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= 22208u64; };
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk.len() by close() using { to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer(at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) - 4u64); 4u64 <= at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)); at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= remainder_chunk.len(); };
        apply(adler_bounded_pointer_association(remainder_chunk, (((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))));
        have to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk.len() as u32) as i32) - at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) + 4) by close() using { to_integer(((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) - 4); 4 <= at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; };
        have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32));
        // A advances at the uint64 cursor, using the real iterator state.
        have to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4) == to_integer(((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)) by close() using { 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32); ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32); ((remainder_chunk.len() as u32) as i32) <= 22204; 0 <= to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4)); };
        have defined((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by close();
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a)) by {
         rewrite(to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64));
         rewrite(to_integer(a_vec.0[0]), to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])));
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
         close();
        }
        have to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by { rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4), to_integer(((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))); close(); }
        have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by {
         have to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by close() using { to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4); };
         rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))), to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4));
         have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); };
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
         have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); };
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
         have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); };
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
         have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))) by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))); };
         rewrite(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))));
         have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))) by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))); };
         rewrite(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))));
         have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))) by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))); };
         rewrite(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))));
         have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))) by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))); };
         rewrite(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))));
         close();
        }
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32)))) by {
         rewrite(to_integer(((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))), to_integer(((bytes.len()) - at(lane_head, adler_chunk_bytes(loop(2).iter.len(), 4u64))) + 4u64));
         have to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4) by close() using { to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4); };
         rewrite(to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))), to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) - 4) + 4));
         have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); };
         rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
         have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); };
         rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
         have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); };
         rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
         have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))) by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))); };
         rewrite(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))));
         have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))) by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))); };
         rewrite(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))));
         have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))) by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))); };
         rewrite(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))));
         have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))) by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))); };
         rewrite(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))));
         close();
        }
        // The invariants at the back edge, one pass further on.
        have loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64));
        have to_integer(loop(2).iter.len()) + (iterations + 1) == to_integer(remainder_chunk.len() / 4u64) by close() using { loop(2).iter.len() == at(lane_head, loop(2).iter.len()) - 1u64; 0u64 < at(lane_head, loop(2).iter.len()); to_integer(at(lane_head, loop(2).iter.len())) + iterations == to_integer(remainder_chunk.len() / 4u64); };
        have loop(2).iter.len() <= remainder_chunk.len() / 4u64 by close() using { to_integer(loop(2).iter.len()) + (iterations + 1) == to_integer(remainder_chunk.len() / 4u64); 0 <= iterations; };
        have remainder_chunk.len() % 4u64 == 0u64;
        have remainder_chunk.len() <= 22204u64;
        // Every invariant at the back edge.
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64;
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a));
        have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
        have 0 <= old(to_integer((self.b as u32)));
        have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk.len();
        have remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
        have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64));
        have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len()));
        have to_integer((bytes.len())) <= to_integer(bytes.len());
        have bytes.len() % 4u64 <= bytes.len();
        have bytes.as_ptr() == old(bytes.as_ptr());
        have bytes.len() == old(bytes.len() - bytes.len() % 4u64);
        have a <= 65520u32;
        have b <= 65520u32;
        have 0 <= ((remainder_chunk.len() as u32) as i32);
        have ((remainder_chunk.len() as u32) as i32) <= 22204;
        have ((remainder_chunk.len() as u32) as i32) % 4 == 0;
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32);
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have remainder_chunk.len() == (bytes.len()) % 22208u64;
        have remainder.len() == old(bytes.len() % 4u64);
        have loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64));
        have to_integer(loop(2).iter.len()) + (iterations + 1) == to_integer(remainder_chunk.len() / 4u64);
        have remainder_chunk.len() % 4u64 == 0u64;
        have remainder_chunk.len() <= 22204u64;
        // The ranking members: the measure is read at the pass entry, before the header ran.
        have at(lane_head, loop(2).iter.len()) == at(remainder_pass, loop(2).iter.len());
        have loop(2).iter.len() < at(lane_head, loop(2).iter.len()) by close() using { loop(2).iter.len() == at(lane_head, loop(2).iter.len()) - 1u64; 0u64 < at(lane_head, loop(2).iter.len()); };
        have loop(2).iter.len() < at(remainder_pass, loop(2).iter.len()) by close() using { loop(2).iter.len() < at(lane_head, loop(2).iter.len()); at(lane_head, loop(2).iter.len()) == at(remainder_pass, loop(2).iter.len()); };
       } else {
        // No chunk is left: the header test fails and the loop leaves by `break`.
        step();
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 22208u64;
        have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a));
        have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
        have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64), to_integer(a), old(to_integer((self.b as u32))));
        have 0 <= old(to_integer((self.b as u32)));
        have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
        have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= remainder_chunk.len();
        have remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len()) - (bytes.len()) % 22208u64);
        have (remainder_chunk.as_ptr() + (((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32))) == bytes.as_ptr() + ((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64));
        have to_integer(adler_chunk_bytes(loop(2).iter.len(), 4u64)) <= to_integer((bytes.len()));
        have to_integer((bytes.len())) <= to_integer(bytes.len());
        have bytes.len() % 4u64 <= bytes.len();
        have bytes.as_ptr() == old(bytes.as_ptr());
        have bytes.len() == old(bytes.len() - bytes.len() % 4u64);
        have a <= 65520u32;
        have b <= 65520u32;
        have 0 <= ((remainder_chunk.len() as u32) as i32);
        have ((remainder_chunk.len() as u32) as i32) <= 22204;
        have ((remainder_chunk.len() as u32) as i32) % 4 == 0;
        have 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= ((remainder_chunk.len() as u32) as i32);
        have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0;
        have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
        have remainder_chunk.len() == (bytes.len()) % 22208u64;
        have remainder.len() == old(bytes.len() % 4u64);
        have loop(2).iter.v == remainder_chunk.as_ptr() + (remainder_chunk.len() - adler_chunk_bytes(loop(2).iter.len(), 4u64));
        have to_integer(loop(2).iter.len()) + iterations == to_integer(remainder_chunk.len() / 4u64);
        have remainder_chunk.len() % 4u64 == 0u64;
        have remainder_chunk.len() <= 22204u64;
        step();
       }
      }
     }
     have loop(2).iter.len() == 0u64;
     apply(adler_chunk_bytes_none(4u64));
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) == 0u64 by { rewrite(loop(2).iter.len(), 0u64); close(); }
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) < 4u64 by close() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) == 0u64; };
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 3u64 by close() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) < 4u64; };
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 2147483647u64 by close() using { adler_chunk_bytes(loop(2).iter.len(), 4u64) <= 3u64; };
     apply(adler_bounded_count_upper(adler_chunk_bytes(loop(2).iter.len(), 4u64), 3));
     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) < 4 by close() using { ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) <= 3; };

     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) by close() using { 0 <= ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32); ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) < 4; };
     have ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) == 0 by close() using { ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == 0; ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) % 4 == ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32); };
     apply(adler_bounded_count(adler_chunk_bytes(loop(2).iter.len(), 4u64)));
     have adler_chunk_bytes(loop(2).iter.len(), 4u64) == 0u64 by close() using { (((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) as uint64) == adler_chunk_bytes(loop(2).iter.len(), 4u64); ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32) == 0; };

     have to_integer((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64)) == to_integer((bytes.len())) by { rewrite(adler_chunk_bytes(loop(2).iter.len(), 4u64), 0u64); close(); }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()), to_integer(a)) by { rewrite(to_integer((bytes.len())), to_integer((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); close(); }
     apply(adler_complete_remainder_position(((remainder_chunk.len() as u32) as i32), ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)));
     have 0 <= adler_lane_b(to_integer(b) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(to_integer(((remainder_chunk.len() as u32) as i32)), to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); close(); }
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(to_integer(((remainder_chunk.len() as u32) as i32)), to_integer((((remainder_chunk.len() as u32) as i32) - ((adler_chunk_bytes(loop(2).iter.len(), 4u64) as uint32) as int32)))); rewrite(to_integer((bytes.len())), to_integer((bytes.len()) - adler_chunk_bytes(loop(2).iter.len(), 4u64))); close(); }
     mark remainder_lane_prefix;

     have truncating_remainder(adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32))));
     have 0 <= adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3])));
     have truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()), to_integer(at(remainder_lane_prefix, a)));
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
     apply(adler_lane_a_reduction(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))));
     have remainder.len() == old(bytes.len() % 4u64) by close();
     step_until(statement(11).entry);
     have remainder_chunk.len() <= 22204u64 by { rewrite(remainder_chunk.len(), (bytes.len()) % 22208u64); close(); }
     apply(adler_small_length_cast(remainder_chunk.len()));
     have (remainder_chunk.len() as u32) <= 22204u32 by { rewrite((remainder_chunk.len() as u32), (remainder_chunk.len() as u32)); close(); }
     have a <= 65520u32 by close() using { a <= 65520u32; };
     apply(adler_scalar_batch_product_bound((remainder_chunk.len() as u32), a));
     have to_integer((remainder_chunk.len() as u32)) * to_integer(a) <= 4294967295 by close() using { to_integer((remainder_chunk.len() as u32)) * to_integer(a) <= 1454806080; };
     apply(integer::uint32_multiply_guard_by_integer_bound((remainder_chunk.len() as u32), a));
     have remainder_chunk.len() <= 22208u64 by close() using { remainder_chunk.len() <= 22204u64; };
     apply(adler_count_observation(remainder_chunk.len()));
     apply(adler_remainder_native_count_observation(remainder_chunk.len()));
     have to_integer((remainder_chunk.len() as u32)) == to_integer(((remainder_chunk.len() as u32) as i32)) by { rewrite((remainder_chunk.len() as u32), (remainder_chunk.len() as u32)); close() using { to_integer((remainder_chunk.len() as u32)) == to_integer(remainder_chunk.len()); to_integer(((remainder_chunk.len() as u32) as i32)) == to_integer(remainder_chunk.len()); }; }
     mark seed_product;
     have to_integer(at(seed_product, (remainder_chunk.len() as u32))) == to_integer(((remainder_chunk.len() as u32) as i32));
     have to_integer(at(seed_product, a)) == to_integer(at(remainder_lane_prefix, a));
     have to_integer(at(seed_product, (remainder_chunk.len() as u32))) * to_integer(at(seed_product, a)) <= 1454806080 by close() using { to_integer((remainder_chunk.len() as u32)) * to_integer(a) <= 1454806080; };
     have at(seed_product, a) == 0u32 or at(seed_product, (remainder_chunk.len() as u32)) <= 4294967295u32 / at(seed_product, a) by close() using { a == 0u32 or (remainder_chunk.len() as u32) <= 4294967295u32 / a; };
     apply(integer::uint32_multiply_to_integer(at(seed_product, (remainder_chunk.len() as u32)), at(seed_product, a)));
     have to_integer(at(seed_product, ((remainder_chunk.len() as u32) * a))) == to_integer(at(seed_product, (remainder_chunk.len() as u32)) * at(seed_product, a));
     have to_integer(at(seed_product, ((remainder_chunk.len() as u32) * a))) == to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)) by { rewrite(to_integer(at(seed_product, ((remainder_chunk.len() as u32) * a))), to_integer(at(seed_product, (remainder_chunk.len() as u32)) * at(seed_product, a))); rewrite(to_integer(at(seed_product, (remainder_chunk.len() as u32)) * at(seed_product, a)), to_integer(at(seed_product, (remainder_chunk.len() as u32))) * to_integer(at(seed_product, a))); rewrite(to_integer(at(seed_product, (remainder_chunk.len() as u32))), to_integer(((remainder_chunk.len() as u32) as i32))); rewrite(to_integer(at(seed_product, a)), to_integer(at(remainder_lane_prefix, a))); close(); }
     have to_integer(at(seed_product, ((remainder_chunk.len() as u32) * a))) <= 1454806080 by { rewrite(to_integer(at(seed_product, ((remainder_chunk.len() as u32) * a))), to_integer(at(seed_product, (remainder_chunk.len() as u32)) * at(seed_product, a))); rewrite(to_integer(at(seed_product, (remainder_chunk.len() as u32)) * at(seed_product, a)), to_integer(at(seed_product, (remainder_chunk.len() as u32))) * to_integer(at(seed_product, a))); close(); }
     have b <= 65520u32 by close();
     have to_integer(b) + to_integer(at(seed_product, ((remainder_chunk.len() as u32) * a))) <= 4294967295 by close() using { to_integer(b) <= 65520; to_integer(at(seed_product, ((remainder_chunk.len() as u32) * a))) <= 1454806080; };
     have b <= 4294967295u32 - at(seed_product, ((remainder_chunk.len() as u32) * a)) by close() using { to_integer(b) + to_integer(at(seed_product, ((remainder_chunk.len() as u32) * a))) <= 4294967295; };
     mark deferred_b;
     have to_integer(at(deferred_b, b)) == to_integer(at(remainder_lane_prefix, b));
     have to_integer(at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))) == to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a));
     have to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))) <= 4294967295 by close() using { to_integer(b) + to_integer(at(seed_product, ((remainder_chunk.len() as u32) * a))) <= 4294967295; };
     have to_integer(at(deferred_b, b) + at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))) == to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))) by apply(integer::uint32_add_to_integer(at(deferred_b, b), at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))));
     step_until(statement(12).entry);
     mark reduction_a;
     have to_integer(at(reduction_a, a_vec.0[0])) == to_integer(at(remainder_lane_prefix, a_vec.0[0]));
     have to_integer(at(reduction_a, a_vec.0[1])) == to_integer(at(remainder_lane_prefix, a_vec.0[1]));
     have to_integer(at(reduction_a, a_vec.0[2])) == to_integer(at(remainder_lane_prefix, a_vec.0[2]));
     have to_integer(at(reduction_a, a_vec.0[3])) == to_integer(at(remainder_lane_prefix, a_vec.0[3]));
     step_until(statement(13).entry);
     mark reduction_b;
     have to_integer(at(reduction_b, b_vec.0[0])) == to_integer(at(remainder_lane_prefix, b_vec.0[0]));
     have to_integer(at(reduction_b, b_vec.0[1])) == to_integer(at(remainder_lane_prefix, b_vec.0[1]));
     have to_integer(at(reduction_b, b_vec.0[2])) == to_integer(at(remainder_lane_prefix, b_vec.0[2]));
     have to_integer(at(reduction_b, b_vec.0[3])) == to_integer(at(remainder_lane_prefix, b_vec.0[3]));
     step_until(statement(14).entry);
     mark before_scalar_mod;
     step_until(statement(15).entry);
     have to_integer(at(before_scalar_mod, b)) == to_integer(at(deferred_b, b) + at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a))));
     have to_integer(at(before_scalar_mod, b)) == to_integer(at(deferred_b, b) + at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))) by close() using { to_integer(at(before_scalar_mod, b)) == to_integer(at(deferred_b, b) + at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))); };
     have to_integer(at(before_scalar_mod, b)) == to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)) by close() using { to_integer(at(before_scalar_mod, b)) == to_integer(at(deferred_b, b) + at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))); to_integer(at(deferred_b, b) + at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))) == to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))); to_integer(at(deferred_b, b)) == to_integer(at(remainder_lane_prefix, b)); to_integer(at(deferred_b, at(seed_product, ((remainder_chunk.len() as u32) * a)))) == to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)); };

     have 0 <= to_integer(at(before_scalar_mod, b));
     have to_integer(at(before_scalar_mod, b)) <= 4294967295;
     have 0 <= to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)) by close() using { 0 <= to_integer(at(before_scalar_mod, b)); to_integer(at(before_scalar_mod, b)) == to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)); };
     have 0 <= to_integer((at(remainder_lane_prefix, b_vec.0[0])));
     have to_integer((at(remainder_lane_prefix, b_vec.0[0]))) <= 4294967295;
     have 0 <= to_integer((at(remainder_lane_prefix, b_vec.0[1])));
     have to_integer((at(remainder_lane_prefix, b_vec.0[1]))) <= 4294967295;
     have 0 <= to_integer((at(remainder_lane_prefix, b_vec.0[2])));
     have to_integer((at(remainder_lane_prefix, b_vec.0[2]))) <= 4294967295;
     have 0 <= to_integer((at(remainder_lane_prefix, b_vec.0[3])));
     have to_integer((at(remainder_lane_prefix, b_vec.0[3]))) <= 4294967295;
     apply(adler_lane_b_reduction(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))));
     have statement(13).call(0).result == 65521u32;
     have 65521u32 == statement(13).call(0).result by close() using { statement(13).call(0).result == 65521u32; };
     have b_vec.0[0] < statement(13).call(0).result;
     have b_vec.0[0] < 65521u32 by { rewrite(65521u32, statement(13).call(0).result); close(); }
     have b_vec.0[0] <= 4294967295u32 / 4u32 by close() using { b_vec.0[0] < 65521u32; };
     have b_vec.0[1] < statement(13).call(0).result;
     have b_vec.0[1] < 65521u32 by { rewrite(65521u32, statement(13).call(0).result); close(); }
     have b_vec.0[1] <= 4294967295u32 / 4u32 by close() using { b_vec.0[1] < 65521u32; };
     have b_vec.0[2] < statement(13).call(0).result;
     have b_vec.0[2] < 65521u32 by { rewrite(65521u32, statement(13).call(0).result); close(); }
     have b_vec.0[2] <= 4294967295u32 / 4u32 by close() using { b_vec.0[2] < 65521u32; };
     have b_vec.0[3] < statement(13).call(0).result;
     have b_vec.0[3] < 65521u32 by { rewrite(65521u32, statement(13).call(0).result); close(); }
     have b_vec.0[3] <= 4294967295u32 / 4u32 by close() using { b_vec.0[3] < 65521u32; };
     have to_integer(b_vec.0[0]) <= 65520 by close() using { to_integer(b_vec.0[0]) < 65521; };
     have to_integer(b_vec.0[1]) <= 65520 by close() using { to_integer(b_vec.0[1]) < 65521; };
     have to_integer(b_vec.0[2]) <= 65520 by close() using { to_integer(b_vec.0[2]) < 65521; };
     have to_integer(b_vec.0[3]) <= 65520 by close() using { to_integer(b_vec.0[3]) < 65521; };
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a));
     have statement(12).call(0).result == 65521u32;
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % statement(12).call(0).result;
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32 by { rewrite(a_vec.0[0], at(reduction_a, a_vec.0[0]) % statement(12).call(0).result); close() using { statement(12).call(0).result == 65521u32; }; }
     have to_integer(65521u32) != 0 by { close(); }
     apply(integer::uint32_remainder_to_integer(at(reduction_a, a_vec.0[0]), 65521u32));
     have to_integer(a_vec.0[0]) == to_integer(at(reduction_a, a_vec.0[0]) % 65521u32) by close() using { a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[0]))); close(); }
     have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521) by close() using { to_integer(a_vec.0[0]) == to_integer(at(reduction_a, a_vec.0[0]) % 65521u32); to_integer(at(reduction_a, a_vec.0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521); };
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % statement(12).call(0).result;
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32 by { rewrite(a_vec.0[1], at(reduction_a, a_vec.0[1]) % statement(12).call(0).result); close() using { statement(12).call(0).result == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_a, a_vec.0[1]), 65521u32));
     have to_integer(a_vec.0[1]) == to_integer(at(reduction_a, a_vec.0[1]) % 65521u32) by close() using { a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[1]))); close(); }
     have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521) by close() using { to_integer(a_vec.0[1]) == to_integer(at(reduction_a, a_vec.0[1]) % 65521u32); to_integer(at(reduction_a, a_vec.0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521); };
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % statement(12).call(0).result;
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32 by { rewrite(a_vec.0[2], at(reduction_a, a_vec.0[2]) % statement(12).call(0).result); close() using { statement(12).call(0).result == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_a, a_vec.0[2]), 65521u32));
     have to_integer(a_vec.0[2]) == to_integer(at(reduction_a, a_vec.0[2]) % 65521u32) by close() using { a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[2]))); close(); }
     have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521) by close() using { to_integer(a_vec.0[2]) == to_integer(at(reduction_a, a_vec.0[2]) % 65521u32); to_integer(at(reduction_a, a_vec.0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521); };
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % statement(12).call(0).result;
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32 by { rewrite(a_vec.0[3], at(reduction_a, a_vec.0[3]) % statement(12).call(0).result); close() using { statement(12).call(0).result == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_a, a_vec.0[3]), 65521u32));
     have to_integer(a_vec.0[3]) == to_integer(at(reduction_a, a_vec.0[3]) % 65521u32) by close() using { a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[3])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))); close(); }
     have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521) by close() using { to_integer(a_vec.0[3]) == to_integer(at(reduction_a, a_vec.0[3]) % 65521u32); to_integer(at(reduction_a, a_vec.0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521); };
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()), to_integer(at(remainder_lane_prefix, a))) by { rewrite(to_integer(a), to_integer(at(remainder_lane_prefix, a))); rewrite(to_integer(a_vec.0[0]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521)); rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521)); rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521)); rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521)); close() using { truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))), 65521) == truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521)), 65521); truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()), to_integer(at(remainder_lane_prefix, a))); }; }
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % statement(13).call(0).result;
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32 by { rewrite(b_vec.0[0], at(reduction_b, b_vec.0[0]) % statement(13).call(0).result); close() using { statement(13).call(0).result == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_b, b_vec.0[0]), 65521u32));
     have to_integer(b_vec.0[0]) == to_integer(at(reduction_b, b_vec.0[0]) % 65521u32) by close() using { b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[0]))); close(); }
     have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521) by close() using { to_integer(b_vec.0[0]) == to_integer(at(reduction_b, b_vec.0[0]) % 65521u32); to_integer(at(reduction_b, b_vec.0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521); };
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % statement(13).call(0).result;
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32 by { rewrite(b_vec.0[1], at(reduction_b, b_vec.0[1]) % statement(13).call(0).result); close() using { statement(13).call(0).result == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_b, b_vec.0[1]), 65521u32));
     have to_integer(b_vec.0[1]) == to_integer(at(reduction_b, b_vec.0[1]) % 65521u32) by close() using { b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[1]))); close(); }
     have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521) by close() using { to_integer(b_vec.0[1]) == to_integer(at(reduction_b, b_vec.0[1]) % 65521u32); to_integer(at(reduction_b, b_vec.0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521); };
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % statement(13).call(0).result;
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32 by { rewrite(b_vec.0[2], at(reduction_b, b_vec.0[2]) % statement(13).call(0).result); close() using { statement(13).call(0).result == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_b, b_vec.0[2]), 65521u32));
     have to_integer(b_vec.0[2]) == to_integer(at(reduction_b, b_vec.0[2]) % 65521u32) by close() using { b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[2]))); close(); }
     have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521) by close() using { to_integer(b_vec.0[2]) == to_integer(at(reduction_b, b_vec.0[2]) % 65521u32); to_integer(at(reduction_b, b_vec.0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521); };
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % statement(13).call(0).result;
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32 by { rewrite(b_vec.0[3], at(reduction_b, b_vec.0[3]) % statement(13).call(0).result); close() using { statement(13).call(0).result == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(reduction_b, b_vec.0[3]), 65521u32));
     have to_integer(b_vec.0[3]) == to_integer(at(reduction_b, b_vec.0[3]) % 65521u32) by close() using { b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))); close(); }
     have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521) by close() using { to_integer(b_vec.0[3]) == to_integer(at(reduction_b, b_vec.0[3]) % 65521u32); to_integer(at(reduction_b, b_vec.0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521); };
     have statement(14).call(0).result == 65521u32;
     have b == at(before_scalar_mod, b) % statement(14).call(0).result;
     have b == at(before_scalar_mod, b) % 65521u32 by { rewrite(b, at(before_scalar_mod, b) % statement(14).call(0).result); close() using { statement(14).call(0).result == 65521u32; }; }
     apply(integer::uint32_remainder_to_integer(at(before_scalar_mod, b), 65521u32));
     have to_integer(b) == to_integer(at(before_scalar_mod, b) % 65521u32) by close() using { b == at(before_scalar_mod, b) % 65521u32; };
     have truncating_remainder(to_integer(at(before_scalar_mod, b)), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521) by { rewrite(to_integer(at(before_scalar_mod, b)), to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a))); close(); }
     have to_integer(b) == truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521) by close() using { to_integer(b) == to_integer(at(before_scalar_mod, b) % 65521u32); to_integer(at(before_scalar_mod, b) % 65521u32) == truncating_remainder(to_integer(at(before_scalar_mod, b)), to_integer(65521u32)); truncating_remainder(to_integer(at(before_scalar_mod, b)), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521); };
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521)); rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521)); rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521)); rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521)); rewrite(to_integer(b_vec.0[0]), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521)); rewrite(to_integer(b_vec.0[1]), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521)); rewrite(to_integer(b_vec.0[2]), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521)); rewrite(to_integer(b_vec.0[3]), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521)); close() using { truncating_remainder(adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))), 65521) == truncating_remainder(adler_lane_b(truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521)), 65521); truncating_remainder(adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk.len() as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32)))); }; }
     mark weighted_b;
     have truncating_remainder(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))), 65521) == adler_spec_b_u64(bytes.as_ptr(), (bytes.len()), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32))));
     step_until(statement(16).entry);
     have statement(12).call(0).result == 65521u32;
     have 65521u32 == statement(12).call(0).result by close() using { statement(12).call(0).result == 65521u32; };
     have a_vec.0[0] < statement(12).call(0).result;
     have a_vec.0[0] < 65521u32 by { rewrite(65521u32, statement(12).call(0).result); close(); }
     have a_vec.0[1] < statement(12).call(0).result;
     have a_vec.0[1] < 65521u32 by { rewrite(65521u32, statement(12).call(0).result); close(); }
     have a_vec.0[2] < statement(12).call(0).result;
     have a_vec.0[2] < 65521u32 by { rewrite(65521u32, statement(12).call(0).result); close(); }
     have a_vec.0[3] < statement(12).call(0).result;
     have a_vec.0[3] < 65521u32 by { rewrite(65521u32, statement(12).call(0).result); close(); }
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have to_integer(at(weighted_b, b_vec.0[0])) <= 65520;
     have to_integer(b_vec.0[0]) <= 262080 by close() using { to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4; to_integer(at(weighted_b, b_vec.0[0])) <= 65520; };
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(at(weighted_b, b_vec.0[1])) <= 65520;
     have to_integer(b_vec.0[1]) <= 262080 by close() using { to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4; to_integer(at(weighted_b, b_vec.0[1])) <= 65520; };
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(at(weighted_b, b_vec.0[2])) <= 65520;
     have to_integer(b_vec.0[2]) <= 262080 by close() using { to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4; to_integer(at(weighted_b, b_vec.0[2])) <= 65520; };
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(at(weighted_b, b_vec.0[3])) <= 65520;
     have to_integer(b_vec.0[3]) <= 262080 by close() using { to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4; to_integer(at(weighted_b, b_vec.0[3])) <= 65520; };
     mark correction_b;
     have to_integer(at(correction_b, b_vec.0[1])) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(at(correction_b, a_vec.0[1])) == to_integer(at(weighted_b, a_vec.0[1]));
     have to_integer(at(correction_b, b_vec.0[2])) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(at(correction_b, a_vec.0[2])) == to_integer(at(weighted_b, a_vec.0[2]));
     have to_integer(at(correction_b, b_vec.0[3])) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(at(correction_b, a_vec.0[3])) == to_integer(at(weighted_b, a_vec.0[3]));
     apply(adler_recombine_lane_1(a_vec.0[1], b_vec.0[1]));
     apply(adler_recombine_lane_2(a_vec.0[2], b_vec.0[2]));
     apply(adler_recombine_lane_3(a_vec.0[3], b_vec.0[3]));
     apply(adler_recombine_difference(a_vec.0[1]));
     apply(adler_recombine_difference(a_vec.0[2]));
     have 65521u32 - a_vec.0[2] <= 4294967295u32 / 2u32 by {
      have to_integer(65521u32) <= to_integer(4294967295u32 / 2u32) by close();
      apply(integer::le_transitive(to_integer(65521u32 - a_vec.0[2]), to_integer(65521u32), to_integer(4294967295u32 / 2u32)));
      apply(integer::uint32_to_integer_less_equal_implies_less_equal(65521u32 - a_vec.0[2], 4294967295u32 / 2u32));
     }
     apply(adler_recombine_difference(a_vec.0[3]));
     have 65521u32 - a_vec.0[3] <= 4294967295u32 / 3u32 by {
      have to_integer(65521u32) <= to_integer(4294967295u32 / 3u32) by close();
      apply(integer::le_transitive(to_integer(65521u32 - a_vec.0[3]), to_integer(65521u32), to_integer(4294967295u32 / 3u32)));
      apply(integer::uint32_to_integer_less_equal_implies_less_equal(65521u32 - a_vec.0[3], 4294967295u32 / 3u32));
     }
     have to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) == to_integer(at(correction_b, b_vec.0[1])) + (65521 - to_integer(at(correction_b, a_vec.0[1]))) * 1;
     have to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) == to_integer(at(correction_b, b_vec.0[2])) + (65521 - to_integer(at(correction_b, a_vec.0[2]))) * 2;
     have to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) == to_integer(at(correction_b, b_vec.0[3])) + (65521 - to_integer(at(correction_b, a_vec.0[3]))) * 3;
     have separate(memory(b_vec.0[1..2]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     have separate(memory(((((b_vec as (uint8 *)) + 4) as (uint32 *)))[0..1]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     step_until(statement(17).entry);
     have statement(16).call(0).result == 65521u32;
     have separate(memory(b_vec.0[2..3]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     have separate(memory(((((b_vec as (uint8 *)) + 8) as (uint32 *)))[0..1]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     step_until(statement(18).entry);
     have statement(17).call(0).result == 65521u32;
     have separate(memory(b_vec.0[3..4]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     have separate(memory(((((b_vec as (uint8 *)) + 12) as (uint32 *)))[0..1]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     step_until(statement(19).entry);
     have statement(18).call(0).result == 65521u32;
     step_until(loop(3).entry);
     have b_vec.0[1] == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1])) by close();
     have to_integer(b_vec.0[1]) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) by {
      apply(adler_equal_stored_words(b_vec.0[1], at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))));
     }
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[1]))) * 1 by {
      rewrite(to_integer(b_vec.0[1]), to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))));
      rewrite(to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))), to_integer(at(correction_b, b_vec.0[1])) + (65521 - to_integer(at(correction_b, a_vec.0[1]))) * 1);
      rewrite(to_integer(at(correction_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[1])) * 4);
      rewrite(to_integer(at(correction_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[1])));
      close();
     }
     have b_vec.0[2] == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32) by close();
     have to_integer(b_vec.0[2]) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) by {
      apply(adler_equal_stored_words(b_vec.0[2], at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)));
     }
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[2]))) * 2 by {
      rewrite(to_integer(b_vec.0[2]), to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)));
      rewrite(to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)), to_integer(at(correction_b, b_vec.0[2])) + (65521 - to_integer(at(correction_b, a_vec.0[2]))) * 2);
      rewrite(to_integer(at(correction_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[2])) * 4);
      rewrite(to_integer(at(correction_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[2])));
      close();
     }
     have b_vec.0[3] == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32) by close();
     have to_integer(b_vec.0[3]) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) by {
      apply(adler_equal_stored_words(b_vec.0[3], at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)));
     }
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[3]))) * 3 by {
      rewrite(to_integer(b_vec.0[3]), to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)));
      rewrite(to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)), to_integer(at(correction_b, b_vec.0[3])) + (65521 - to_integer(at(correction_b, a_vec.0[3]))) * 3);
      rewrite(to_integer(at(correction_b, b_vec.0[3])), to_integer(at(weighted_b, b_vec.0[3])) * 4);
      rewrite(to_integer(at(correction_b, a_vec.0[3])), to_integer(at(weighted_b, a_vec.0[3])));
      close();
     }
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have a <= 65520u32 by close();
     step_until(loop(3).statement(0).entry);
     have av == a_vec.0[0];
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[0]); close() using { to_integer(a_vec.0[0]) < 65521; }; }
     have to_integer(av) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(av) <= 4294967295 by close() using { to_integer(a) <= 65520; to_integer(av) <= 65520; };
     have a <= 4294967295u32 - av by close() using { to_integer(a) + to_integer(av) <= 4294967295; };
     mark remainder_sum_a_0;
     have to_integer(at(remainder_sum_a_0, a)) == to_integer(at(remainder_lane_prefix, a));
     have to_integer(at(remainder_sum_a_0, av)) == to_integer(a_vec.0[0]);
     have to_integer(at(remainder_sum_a_0, a)) <= 65520 by close() using { to_integer(a) <= 65520; };
     have to_integer(at(remainder_sum_a_0, av)) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, av)) <= 4294967295 by close() using { to_integer(at(remainder_sum_a_0, a)) <= 65520; to_integer(at(remainder_sum_a_0, av)) <= 65520; };
     have to_integer(at(remainder_sum_a_0, (a + av))) == to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, av));
     have to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, av)) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, av)) by apply(integer::uint32_add_to_integer(at(remainder_sum_a_0, a), at(remainder_sum_a_0, av)));
     have to_integer(at(remainder_sum_a_0, (a + av))) <= 131040 by { rewrite(to_integer(at(remainder_sum_a_0, (a + av))), to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, av))); rewrite(to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, av)), to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, av))); close() using { to_integer(at(remainder_sum_a_0, a)) <= 65520; to_integer(at(remainder_sum_a_0, av)) <= 65520; }; }
     step_until(assignment(a, 1).entry); step();
     have to_integer(a) <= 131040 by close() using { to_integer(at(remainder_sum_a_0, (a + av))) <= 131040; };
     have to_integer(at(remainder_sum_a_0, (a + av))) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, av)) by close() using { to_integer(at(remainder_sum_a_0, (a + av))) == to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, av)); to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, av)) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, av)); };
     have to_integer(a) == to_integer(at(remainder_sum_a_0, (a + av)));
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) by close() using { to_integer(a) == to_integer(at(remainder_sum_a_0, (a + av))); to_integer(at(remainder_sum_a_0, (a + av))) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, av)); to_integer(at(remainder_sum_a_0, a)) == to_integer(at(remainder_lane_prefix, a)); to_integer(at(remainder_sum_a_0, av)) == to_integer(a_vec.0[0]); };

     step_until(loop(3).statement(0).entry);
     have av == a_vec.0[1];
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[1]); close() using { to_integer(a_vec.0[1]) < 65521; }; }
     have to_integer(av) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(av) <= 4294967295 by close() using { to_integer(a) <= 131040; to_integer(av) <= 65520; };
     have a <= 4294967295u32 - av by close() using { to_integer(a) + to_integer(av) <= 4294967295; };
     mark remainder_sum_a_1;
     have to_integer(at(remainder_sum_a_1, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]);
     have to_integer(at(remainder_sum_a_1, av)) == to_integer(a_vec.0[1]);
     have to_integer(at(remainder_sum_a_1, a)) <= 131040 by close() using { to_integer(a) <= 131040; };
     have to_integer(at(remainder_sum_a_1, av)) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, av)) <= 4294967295 by close() using { to_integer(at(remainder_sum_a_1, a)) <= 131040; to_integer(at(remainder_sum_a_1, av)) <= 65520; };
     have to_integer(at(remainder_sum_a_1, (a + av))) == to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, av));
     have to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, av)) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, av)) by apply(integer::uint32_add_to_integer(at(remainder_sum_a_1, a), at(remainder_sum_a_1, av)));
     have to_integer(at(remainder_sum_a_1, (a + av))) <= 196560 by { rewrite(to_integer(at(remainder_sum_a_1, (a + av))), to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, av))); rewrite(to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, av)), to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, av))); close() using { to_integer(at(remainder_sum_a_1, a)) <= 131040; to_integer(at(remainder_sum_a_1, av)) <= 65520; }; }
     step_until(assignment(a, 1).entry); step();
     have to_integer(a) <= 196560 by close() using { to_integer(at(remainder_sum_a_1, (a + av))) <= 196560; };
     have to_integer(at(remainder_sum_a_1, (a + av))) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, av)) by close() using { to_integer(at(remainder_sum_a_1, (a + av))) == to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, av)); to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, av)) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, av)); };
     have to_integer(a) == to_integer(at(remainder_sum_a_1, (a + av)));
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) by close() using { to_integer(a) == to_integer(at(remainder_sum_a_1, (a + av))); to_integer(at(remainder_sum_a_1, (a + av))) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, av)); to_integer(at(remainder_sum_a_1, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]); to_integer(at(remainder_sum_a_1, av)) == to_integer(a_vec.0[1]); };

     step_until(loop(3).statement(0).entry);
     have av == a_vec.0[2];
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[2]); close() using { to_integer(a_vec.0[2]) < 65521; }; }
     have to_integer(av) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(av) <= 4294967295 by close() using { to_integer(a) <= 196560; to_integer(av) <= 65520; };
     have a <= 4294967295u32 - av by close() using { to_integer(a) + to_integer(av) <= 4294967295; };
     mark remainder_sum_a_2;
     have to_integer(at(remainder_sum_a_2, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]);
     have to_integer(at(remainder_sum_a_2, av)) == to_integer(a_vec.0[2]);
     have to_integer(at(remainder_sum_a_2, a)) <= 196560 by close() using { to_integer(a) <= 196560; };
     have to_integer(at(remainder_sum_a_2, av)) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, av)) <= 4294967295 by close() using { to_integer(at(remainder_sum_a_2, a)) <= 196560; to_integer(at(remainder_sum_a_2, av)) <= 65520; };
     have to_integer(at(remainder_sum_a_2, (a + av))) == to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, av));
     have to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, av)) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, av)) by apply(integer::uint32_add_to_integer(at(remainder_sum_a_2, a), at(remainder_sum_a_2, av)));
     have to_integer(at(remainder_sum_a_2, (a + av))) <= 262080 by { rewrite(to_integer(at(remainder_sum_a_2, (a + av))), to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, av))); rewrite(to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, av)), to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, av))); close() using { to_integer(at(remainder_sum_a_2, a)) <= 196560; to_integer(at(remainder_sum_a_2, av)) <= 65520; }; }
     step_until(assignment(a, 1).entry); step();
     have to_integer(a) <= 262080 by close() using { to_integer(at(remainder_sum_a_2, (a + av))) <= 262080; };
     have to_integer(at(remainder_sum_a_2, (a + av))) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, av)) by close() using { to_integer(at(remainder_sum_a_2, (a + av))) == to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, av)); to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, av)) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, av)); };
     have to_integer(a) == to_integer(at(remainder_sum_a_2, (a + av)));
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) by close() using { to_integer(a) == to_integer(at(remainder_sum_a_2, (a + av))); to_integer(at(remainder_sum_a_2, (a + av))) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, av)); to_integer(at(remainder_sum_a_2, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]); to_integer(at(remainder_sum_a_2, av)) == to_integer(a_vec.0[2]); };

     step_until(loop(3).statement(0).entry);
     have av == a_vec.0[3];
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[3]); close() using { to_integer(a_vec.0[3]) < 65521; }; }
     have to_integer(av) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(av) <= 4294967295 by close() using { to_integer(a) <= 262080; to_integer(av) <= 65520; };
     have a <= 4294967295u32 - av by close() using { to_integer(a) + to_integer(av) <= 4294967295; };
     mark remainder_sum_a_3;
     have to_integer(at(remainder_sum_a_3, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]);
     have to_integer(at(remainder_sum_a_3, av)) == to_integer(a_vec.0[3]);
     have to_integer(at(remainder_sum_a_3, a)) <= 262080 by close() using { to_integer(a) <= 262080; };
     have to_integer(at(remainder_sum_a_3, av)) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, av)) <= 4294967295 by close() using { to_integer(at(remainder_sum_a_3, a)) <= 262080; to_integer(at(remainder_sum_a_3, av)) <= 65520; };
     have to_integer(at(remainder_sum_a_3, (a + av))) == to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, av));
     have to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, av)) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, av)) by apply(integer::uint32_add_to_integer(at(remainder_sum_a_3, a), at(remainder_sum_a_3, av)));
     have to_integer(at(remainder_sum_a_3, (a + av))) <= 327600 by { rewrite(to_integer(at(remainder_sum_a_3, (a + av))), to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, av))); rewrite(to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, av)), to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, av))); close() using { to_integer(at(remainder_sum_a_3, a)) <= 262080; to_integer(at(remainder_sum_a_3, av)) <= 65520; }; }
     step_until(assignment(a, 1).entry); step();
     have to_integer(a) <= 327600 by close() using { to_integer(at(remainder_sum_a_3, (a + av))) <= 327600; };
     have to_integer(at(remainder_sum_a_3, (a + av))) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, av)) by close() using { to_integer(at(remainder_sum_a_3, (a + av))) == to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, av)); to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, av)) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, av)); };
     have to_integer(a) == to_integer(at(remainder_sum_a_3, (a + av)));
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) + to_integer(a_vec.0[3]) by close() using { to_integer(a) == to_integer(at(remainder_sum_a_3, (a + av))); to_integer(at(remainder_sum_a_3, (a + av))) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, av)); to_integer(at(remainder_sum_a_3, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]); to_integer(at(remainder_sum_a_3, av)) == to_integer(a_vec.0[3]); };

     have to_integer(a) == adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) by { unfold(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); close(); }
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes.as_ptr(), (bytes.len()), to_integer(at(remainder_lane_prefix, a))) by { rewrite(to_integer(a), adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); close(); }
     step_until(loop(4).entry);
     have statement(14).call(0).result == 65521u32;
     have 65521u32 == statement(14).call(0).result by close() using { statement(14).call(0).result == 65521u32; };
     have b == at(before_scalar_mod, b) % statement(14).call(0).result;
     have statement(14).call(0).result != 0u32 by { rewrite(statement(14).call(0).result, 65521u32); close(); }
     apply(integer::uint32_remainder_less_than_divisor(at(before_scalar_mod, b), statement(14).call(0).result));
     have b < statement(14).call(0).result by { rewrite(b, at(before_scalar_mod, b) % statement(14).call(0).result); close(); }
     have b < 65521u32 by { rewrite(65521u32, statement(14).call(0).result); close(); }
     have to_integer(b) <= 65520 by close() using { to_integer(b) < 65521; };
     have to_integer(b_vec.0[0]) <= 262080;
     step_until(loop(4).statement(0).entry);
     have bv == b_vec.0[0];
     have to_integer(bv) <= 262080 by { rewrite(bv, b_vec.0[0]); close(); }
     have to_integer(bv) <= 262080 by close() using { to_integer(bv) <= 262080; };
     have to_integer(b) + to_integer(bv) <= 4294967295 by close() using { to_integer(b) <= 65520; to_integer(bv) <= 262080; };
     have b <= 4294967295u32 - bv by close() using { to_integer(b) + to_integer(bv) <= 4294967295; };
     mark remainder_sum_b_0;
     have to_integer(at(remainder_sum_b_0, b)) == to_integer(at(weighted_b, b));
     have to_integer(at(remainder_sum_b_0, bv)) == to_integer(b_vec.0[0]);
     have to_integer(at(remainder_sum_b_0, b)) <= 65520 by close() using { to_integer(b) <= 65520; };
     have to_integer(at(remainder_sum_b_0, bv)) <= 262080 by close() using { to_integer(bv) <= 262080; };
     have to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, bv)) <= 4294967295 by close() using { to_integer(at(remainder_sum_b_0, b)) <= 65520; to_integer(at(remainder_sum_b_0, bv)) <= 262080; };
     have to_integer(at(remainder_sum_b_0, (b + bv))) == to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, bv));
     have to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, bv)) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, bv)) by apply(integer::uint32_add_to_integer(at(remainder_sum_b_0, b), at(remainder_sum_b_0, bv)));
     have to_integer(at(remainder_sum_b_0, (b + bv))) <= 327600 by { rewrite(to_integer(at(remainder_sum_b_0, (b + bv))), to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, bv))); rewrite(to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, bv)), to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, bv))); close() using { to_integer(at(remainder_sum_b_0, b)) <= 65520; to_integer(at(remainder_sum_b_0, bv)) <= 262080; }; }
     step_until(assignment(b, 5).entry); step();
     have to_integer(b) <= 327600 by close() using { to_integer(at(remainder_sum_b_0, (b + bv))) <= 327600; };
     have to_integer(at(remainder_sum_b_0, (b + bv))) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, bv)) by close() using { to_integer(at(remainder_sum_b_0, (b + bv))) == to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, bv)); to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, bv)) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, bv)); };
     have to_integer(b) == to_integer(at(remainder_sum_b_0, (b + bv)));
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) by close() using { to_integer(b) == to_integer(at(remainder_sum_b_0, (b + bv))); to_integer(at(remainder_sum_b_0, (b + bv))) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, bv)); to_integer(at(remainder_sum_b_0, b)) == to_integer(at(weighted_b, b)); to_integer(at(remainder_sum_b_0, bv)) == to_integer(b_vec.0[0]); };

     have to_integer(b_vec.0[1]) <= 327601;
     step_until(loop(4).statement(0).entry);
     have bv == b_vec.0[1];
     have to_integer(bv) <= 327601 by { rewrite(bv, b_vec.0[1]); close(); }
     have to_integer(bv) <= 327601 by close() using { to_integer(bv) <= 327601; };
     have to_integer(b) + to_integer(bv) <= 4294967295 by close() using { to_integer(b) <= 327600; to_integer(bv) <= 327601; };
     have b <= 4294967295u32 - bv by close() using { to_integer(b) + to_integer(bv) <= 4294967295; };
     mark remainder_sum_b_1;
     have to_integer(at(remainder_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]);
     have to_integer(at(remainder_sum_b_1, bv)) == to_integer(b_vec.0[1]);
     have to_integer(at(remainder_sum_b_1, b)) <= 327600 by close() using { to_integer(b) <= 327600; };
     have to_integer(at(remainder_sum_b_1, bv)) <= 327601 by close() using { to_integer(bv) <= 327601; };
     have to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, bv)) <= 4294967295 by close() using { to_integer(at(remainder_sum_b_1, b)) <= 327600; to_integer(at(remainder_sum_b_1, bv)) <= 327601; };
     have to_integer(at(remainder_sum_b_1, (b + bv))) == to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, bv));
     have to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, bv)) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, bv)) by apply(integer::uint32_add_to_integer(at(remainder_sum_b_1, b), at(remainder_sum_b_1, bv)));
     have to_integer(at(remainder_sum_b_1, (b + bv))) <= 655201 by { rewrite(to_integer(at(remainder_sum_b_1, (b + bv))), to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, bv))); rewrite(to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, bv)), to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, bv))); close() using { to_integer(at(remainder_sum_b_1, b)) <= 327600; to_integer(at(remainder_sum_b_1, bv)) <= 327601; }; }
     step_until(assignment(b, 5).entry); step();
     have to_integer(b) <= 655201 by close() using { to_integer(at(remainder_sum_b_1, (b + bv))) <= 655201; };
     have to_integer(at(remainder_sum_b_1, (b + bv))) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, bv)) by close() using { to_integer(at(remainder_sum_b_1, (b + bv))) == to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, bv)); to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, bv)) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, bv)); };
     have to_integer(b) == to_integer(at(remainder_sum_b_1, (b + bv)));
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) by close() using { to_integer(b) == to_integer(at(remainder_sum_b_1, (b + bv))); to_integer(at(remainder_sum_b_1, (b + bv))) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, bv)); to_integer(at(remainder_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]); to_integer(at(remainder_sum_b_1, bv)) == to_integer(b_vec.0[1]); };

     have to_integer(b_vec.0[2]) <= 393122;
     step_until(loop(4).statement(0).entry);
     have bv == b_vec.0[2];
     have to_integer(bv) <= 393122 by { rewrite(bv, b_vec.0[2]); close(); }
     have to_integer(bv) <= 393122 by close() using { to_integer(bv) <= 393122; };
     have to_integer(b) + to_integer(bv) <= 4294967295 by close() using { to_integer(b) <= 655201; to_integer(bv) <= 393122; };
     have b <= 4294967295u32 - bv by close() using { to_integer(b) + to_integer(bv) <= 4294967295; };
     mark remainder_sum_b_2;
     have to_integer(at(remainder_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]);
     have to_integer(at(remainder_sum_b_2, bv)) == to_integer(b_vec.0[2]);
     have to_integer(at(remainder_sum_b_2, b)) <= 655201 by close() using { to_integer(b) <= 655201; };
     have to_integer(at(remainder_sum_b_2, bv)) <= 393122 by close() using { to_integer(bv) <= 393122; };
     have to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, bv)) <= 4294967295 by close() using { to_integer(at(remainder_sum_b_2, b)) <= 655201; to_integer(at(remainder_sum_b_2, bv)) <= 393122; };
     have to_integer(at(remainder_sum_b_2, (b + bv))) == to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, bv));
     have to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, bv)) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, bv)) by apply(integer::uint32_add_to_integer(at(remainder_sum_b_2, b), at(remainder_sum_b_2, bv)));
     have to_integer(at(remainder_sum_b_2, (b + bv))) <= 1048323 by { rewrite(to_integer(at(remainder_sum_b_2, (b + bv))), to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, bv))); rewrite(to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, bv)), to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, bv))); close() using { to_integer(at(remainder_sum_b_2, b)) <= 655201; to_integer(at(remainder_sum_b_2, bv)) <= 393122; }; }
     step_until(assignment(b, 5).entry); step();
     have to_integer(b) <= 1048323 by close() using { to_integer(at(remainder_sum_b_2, (b + bv))) <= 1048323; };
     have to_integer(at(remainder_sum_b_2, (b + bv))) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, bv)) by close() using { to_integer(at(remainder_sum_b_2, (b + bv))) == to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, bv)); to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, bv)) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, bv)); };
     have to_integer(b) == to_integer(at(remainder_sum_b_2, (b + bv)));
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) by close() using { to_integer(b) == to_integer(at(remainder_sum_b_2, (b + bv))); to_integer(at(remainder_sum_b_2, (b + bv))) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, bv)); to_integer(at(remainder_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]); to_integer(at(remainder_sum_b_2, bv)) == to_integer(b_vec.0[2]); };

     have to_integer(b_vec.0[3]) <= 458643;
     step_until(loop(4).statement(0).entry);
     have bv == b_vec.0[3];
     have to_integer(bv) <= 458643 by { rewrite(bv, b_vec.0[3]); close(); }
     have to_integer(bv) <= 458643 by close() using { to_integer(bv) <= 458643; };
     have to_integer(b) + to_integer(bv) <= 4294967295 by close() using { to_integer(b) <= 1048323; to_integer(bv) <= 458643; };
     have b <= 4294967295u32 - bv by close() using { to_integer(b) + to_integer(bv) <= 4294967295; };
     mark remainder_sum_b_3;
     have to_integer(at(remainder_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]);
     have to_integer(at(remainder_sum_b_3, bv)) == to_integer(b_vec.0[3]);
     have to_integer(at(remainder_sum_b_3, b)) <= 1048323 by close() using { to_integer(b) <= 1048323; };
     have to_integer(at(remainder_sum_b_3, bv)) <= 458643 by close() using { to_integer(bv) <= 458643; };
     have to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, bv)) <= 4294967295 by close() using { to_integer(at(remainder_sum_b_3, b)) <= 1048323; to_integer(at(remainder_sum_b_3, bv)) <= 458643; };
     have to_integer(at(remainder_sum_b_3, (b + bv))) == to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, bv));
     have to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, bv)) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, bv)) by apply(integer::uint32_add_to_integer(at(remainder_sum_b_3, b), at(remainder_sum_b_3, bv)));
     have to_integer(at(remainder_sum_b_3, (b + bv))) <= 1506966 by { rewrite(to_integer(at(remainder_sum_b_3, (b + bv))), to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, bv))); rewrite(to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, bv)), to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, bv))); close() using { to_integer(at(remainder_sum_b_3, b)) <= 1048323; to_integer(at(remainder_sum_b_3, bv)) <= 458643; }; }
     step_until(assignment(b, 5).entry); step();
     have to_integer(b) <= 1506966 by close() using { to_integer(at(remainder_sum_b_3, (b + bv))) <= 1506966; };
     have to_integer(at(remainder_sum_b_3, (b + bv))) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, bv)) by close() using { to_integer(at(remainder_sum_b_3, (b + bv))) == to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, bv)); to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, bv)) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, bv)); };
     have to_integer(b) == to_integer(at(remainder_sum_b_3, (b + bv)));
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) + to_integer(b_vec.0[3]) by close() using { to_integer(b) == to_integer(at(remainder_sum_b_3, (b + bv))); to_integer(at(remainder_sum_b_3, (b + bv))) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, bv)); to_integer(at(remainder_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]); to_integer(at(remainder_sum_b_3, bv)) == to_integer(b_vec.0[3]); };

     have remainder.len() == old(bytes.len() % 4u64) by close();
     apply(adler_general_tail_metadata_u64(old(bytes.len())));
     have remainder.len() <= 3u64 by { rewrite(remainder.len(), old(bytes.len()) % 4u64); close(); }
     have remainder.len() <= 2147483647u64 by close() using { remainder.len() <= 3u64; };

     have to_integer(b) == adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))) by { unfold(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3])))); close() using { to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) + to_integer(b_vec.0[3]); to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4; to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[1]))) * 1; to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[2]))) * 2; to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[3]))) * 3; }; }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes.as_ptr(), (old(bytes.len()) - old(bytes.len()) % 4u64), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3])))); close(); }
     step_until(loop(5).entry);
     apply(adler_bounded_count(remainder.len()));
     apply(adler_bounded_count_upper(remainder.len(), 3));
     have 0 <= ((remainder.len() as u32) as i32);
     have ((remainder.len() as u32) as i32) <= 3;
     have ((loop(5).iter.len() as u32) as i32) == ((remainder.len() as u32) as i32) by close() using { remainder.len() <= 3u64; };
     have 0 <= ((loop(5).iter.len() as u32) as i32) and ((loop(5).iter.len() as u32) as i32) <= ((remainder.len() as u32) as i32) by { rewrite(((loop(5).iter.len() as u32) as i32), ((remainder.len() as u32) as i32)); all { 0 <= ((remainder.len() as u32) as i32) => { close(); } ((remainder.len() as u32) as i32) <= ((remainder.len() as u32) as i32) => { close() using {}; } } }
     have adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)) == 0 by { unfold(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32))); rewrite(((loop(5).iter.len() as u32) as i32), ((remainder.len() as u32) as i32)); close() using {}; }
     have adler_tail_a_ceiling(0) == 327600 by { unfold(adler_tail_a_ceiling(0)); close() using {}; }
     have adler_tail_b_ceiling(0) == 1506966 by { unfold(adler_tail_b_ceiling(0)); close() using {}; }
     have 0 <= to_integer(a);
     have to_integer(a) <= 4294967295;
     have 0 <= to_integer(b);
     have to_integer(b) <= 4294967295;
     have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)), 0); rewrite(adler_tail_a_ceiling(0), 327600); close(); }
     have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)), 0); rewrite(adler_tail_b_ceiling(0), 1506966); close(); }
     have remainder.len() <= old(bytes.len()) by { rewrite(remainder.len(), old(bytes.len()) % 4u64); close(); }
     have loop(5).iter.len() == remainder.len();
     have loop(5).iter.len() <= remainder.len() by { rewrite(loop(5).iter.len(), remainder.len()); close(); }
     have remainder.as_ptr() == bytes.as_ptr() + (old(bytes.len()) - old(bytes.len()) % 4u64);
     have to_integer(old(bytes.len()) - loop(5).iter.len()) == to_integer(old(bytes.len()) - old(bytes.len()) % 4u64) by { rewrite(loop(5).iter.len(), remainder.len()); rewrite(remainder.len(), old(bytes.len()) % 4u64); close(); }
     have remainder.as_ptr() == bytes.as_ptr() + (old(bytes.len()) - old(bytes.len()) % 4u64) by close() using { remainder.as_ptr() == remainder; remainder.as_ptr() == bytes.as_ptr() + (old(bytes.len()) - old(bytes.len()) % 4u64); };
     have remainder.len() == old(bytes.len() % 4u64);
     have loop(5).iter.len() <= 3u64;
     // Connect the completed aligned prefix to the actual scalar iterator.
     have old(to_integer((self.a as u32))) == to_integer(at(remainder_lane_prefix, a));
     have 0 <= to_integer((old((self.a as u32))));
     have to_integer((old((self.a as u32)))) <= 4294967295;
     have to_integer((old((self.a as u32)))) <= to_integer(65520u32);
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len(), old(to_integer((self.a as u32)))) by { rewrite(to_integer(old(bytes.len()) - loop(5).iter.len()), to_integer(old(bytes.len()) - old(bytes.len()) % 4u64)); rewrite(old(to_integer((self.a as u32))), to_integer(at(remainder_lane_prefix, a))); close(); }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(old(bytes.len()) - loop(5).iter.len()), to_integer(old(bytes.len()) - old(bytes.len()) % 4u64)); rewrite(old(to_integer((self.a as u32))), to_integer(at(remainder_lane_prefix, a))); close(); }
     loop {
      decreases loop(5).iter.len();
      views bytes[0u64..(bytes.len() + remainder.len())];
      invariant bytes.len() == old(bytes.len() - bytes.len() % 4u64);
      invariant bytes.as_ptr() == old(bytes.as_ptr());
      invariant forall (k: uint64) { k < old(bytes.len()) implies bytes[k] == old(bytes[k]) };
      invariant 0 <= ((remainder.len() as u32) as i32) and ((remainder.len() as u32) as i32) <= 3;
      invariant 0 <= ((loop(5).iter.len() as u32) as i32) and ((loop(5).iter.len() as u32) as i32) <= ((remainder.len() as u32) as i32);
       invariant remainder.len() <= 3u64;
       invariant remainder.len() <= old(bytes.len());
       invariant loop(5).iter.len() <= remainder.len();
       invariant remainder.as_ptr() == bytes.as_ptr() + (old(bytes.len()) - old(bytes.len()) % 4u64);
       invariant remainder.len() == old(bytes.len() % 4u64);
      invariant 0 <= old(to_integer((self.a as u32))) and old(to_integer((self.a as u32))) <= 65520;
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len(), old(to_integer((self.a as u32))));
      invariant truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))));
      invariant 0 <= to_integer(a) and to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)));
      invariant 0 <= to_integer(b) and to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)));
      maintain by {
        have 0u64 < loop(5).iter.len();
        have 1u64 <= loop(5).iter.len() by close() using { 0u64 < loop(5).iter.len(); };
        have loop(5).iter.len() <= 22208u64 by close() using { loop(5).iter.len() <= remainder.len(); remainder.len() <= 3u64; };
        apply(adler_count_tail_step(loop(5).iter.len()));
        have 0 < ((loop(5).iter.len() as u32) as i32) by close() using { 1 <= ((loop(5).iter.len() as u32) as i32); };
       have 1 <= ((loop(5).iter.len() as u32) as i32) by close() using { 0 < ((loop(5).iter.len() as u32) as i32); };
       have 0 <= to_integer(((loop(5).iter.len() as u32) as i32) - 1) by close() using { 0 < ((loop(5).iter.len() as u32) as i32); };
       have to_integer(((loop(5).iter.len() as u32) as i32) - 1) <= to_integer(((remainder.len() as u32) as i32)) by close() using { 0 < ((loop(5).iter.len() as u32) as i32); ((loop(5).iter.len() as u32) as i32) <= ((remainder.len() as u32) as i32); };
       mark tail_head;
       have 1 <= at(tail_head, ((loop(5).iter.len() as u32) as i32));
       have at(tail_head, ((loop(5).iter.len() as u32) as i32)) <= ((remainder.len() as u32) as i32);
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))));
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))));
        have 1u64 <= at(tail_head, loop(5).iter.len());
        have at(tail_head, loop(5).iter.len()) <= remainder.len();
        have to_integer(old(bytes.len()) - at(tail_head, loop(5).iter.len())) < to_integer(old(bytes.len())) by close() using { 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= old(bytes.len()); };
       have truncating_remainder(to_integer(at(tail_head, a)), 65521) == adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()) - at(tail_head, loop(5).iter.len()), old(to_integer((self.a as u32))));
       have truncating_remainder(to_integer(at(tail_head, b)), 65521) == adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()) - at(tail_head, loop(5).iter.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))));
        have old(bytes.len()) % 4u64 <= old(bytes.len()) by close();
        apply(integer::uint64_subtract_to_integer(old(bytes.len()), old(bytes.len()) % 4u64));
        have to_integer(old(bytes.len()) - old(bytes.len()) % 4u64) <= to_integer(old(bytes.len())) by close() using { to_integer(old(bytes.len()) - old(bytes.len()) % 4u64) == to_integer(old(bytes.len())) - to_integer(old(bytes.len()) % 4u64); };
        have old(bytes.len()) - old(bytes.len()) % 4u64 <= old(bytes.len()) by close() using { to_integer(old(bytes.len()) - old(bytes.len()) % 4u64) <= to_integer(old(bytes.len())); };
        apply(integer::uint64_subtract_to_integer(old(bytes.len()), old(bytes.len()) - old(bytes.len()) % 4u64));
        have to_integer(remainder.len()) == to_integer(old(bytes.len()) - (old(bytes.len()) - old(bytes.len()) % 4u64)) by close() using { to_integer(old(bytes.len()) - (old(bytes.len()) - old(bytes.len()) % 4u64)) == to_integer(old(bytes.len())) - to_integer(old(bytes.len()) - old(bytes.len()) % 4u64); to_integer(old(bytes.len()) - old(bytes.len()) % 4u64) == to_integer(old(bytes.len())) - to_integer(old(bytes.len()) % 4u64); remainder.len() == old(bytes.len()) % 4u64; };
        apply(adler_tail_read_offset(old(bytes.len()) - old(bytes.len()) % 4u64, old(bytes.len()), remainder.len(), loop(5).iter.len()));
        // The element this pass yields is `remaining` elements before the end of the scalar tail.
        have at(tail_head, loop(5).iter.as_slice()) == remainder.as_ptr() + (remainder.len() - at(tail_head, loop(5).iter.len()));
        have at(tail_head, loop(5).iter.as_slice()) == bytes.as_ptr() + (old(bytes.len()) - at(tail_head, loop(5).iter.len())) by {
         apply(integer::uint64_subtract_to_integer(remainder.len(), at(tail_head, loop(5).iter.len())));
         have to_integer(at(tail_head, loop(5).iter.len())) <= to_integer(old(bytes.len())) by close() using { at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= old(bytes.len()); };
         apply(integer::uint64_subtract_to_integer(old(bytes.len()), at(tail_head, loop(5).iter.len())));
         have old(bytes.len()) % 4u64 <= old(bytes.len()) by close();
         apply(integer::uint64_subtract_to_integer(old(bytes.len()), old(bytes.len()) % 4u64));
         have to_integer(remainder.len()) == to_integer(old(bytes.len()) % 4u64) by close() using { remainder.len() == old(bytes.len()) % 4u64; };
         have to_integer((old(bytes.len()) - old(bytes.len()) % 4u64)) + to_integer((remainder.len() - at(tail_head, loop(5).iter.len()))) == to_integer((old(bytes.len()) - at(tail_head, loop(5).iter.len()))) by close() using { to_integer(remainder.len() - at(tail_head, loop(5).iter.len())) == to_integer(remainder.len()) - to_integer(at(tail_head, loop(5).iter.len())); to_integer(old(bytes.len()) - at(tail_head, loop(5).iter.len())) == to_integer(old(bytes.len())) - to_integer(at(tail_head, loop(5).iter.len())); to_integer(old(bytes.len()) - old(bytes.len()) % 4u64) == to_integer(old(bytes.len())) - to_integer(old(bytes.len()) % 4u64); to_integer(remainder.len()) == to_integer(old(bytes.len()) % 4u64); };
         have to_integer((old(bytes.len()) - at(tail_head, loop(5).iter.len()))) <= 18446744073709551615;
         have to_integer((old(bytes.len()) - old(bytes.len()) % 4u64)) + to_integer((remainder.len() - at(tail_head, loop(5).iter.len()))) <= 18446744073709551615 by close() using { to_integer((old(bytes.len()) - old(bytes.len()) % 4u64)) + to_integer((remainder.len() - at(tail_head, loop(5).iter.len()))) == to_integer((old(bytes.len()) - at(tail_head, loop(5).iter.len()))); to_integer((old(bytes.len()) - at(tail_head, loop(5).iter.len()))) <= 18446744073709551615; };
         apply(integer::uint64_add_to_integer((old(bytes.len()) - old(bytes.len()) % 4u64), (remainder.len() - at(tail_head, loop(5).iter.len()))));
         have remainder.as_ptr() + (remainder.len() - at(tail_head, loop(5).iter.len())) == bytes.as_ptr() + ((old(bytes.len()) - old(bytes.len()) % 4u64) + (remainder.len() - at(tail_head, loop(5).iter.len()))) by { rewrite(remainder.as_ptr(), bytes.as_ptr() + (old(bytes.len()) - old(bytes.len()) % 4u64)); close() using { to_integer((old(bytes.len()) - old(bytes.len()) % 4u64)) + to_integer((remainder.len() - at(tail_head, loop(5).iter.len()))) <= 18446744073709551615; to_integer((old(bytes.len()) - old(bytes.len()) % 4u64) + (remainder.len() - at(tail_head, loop(5).iter.len()))) == to_integer((old(bytes.len()) - old(bytes.len()) % 4u64)) + to_integer((remainder.len() - at(tail_head, loop(5).iter.len()))); }; }
         have to_integer((old(bytes.len()) - at(tail_head, loop(5).iter.len()))) == to_integer((old(bytes.len()) - old(bytes.len()) % 4u64) + (remainder.len() - at(tail_head, loop(5).iter.len()))) by close() using { to_integer((old(bytes.len()) - old(bytes.len()) % 4u64) + (remainder.len() - at(tail_head, loop(5).iter.len()))) == to_integer((old(bytes.len()) - old(bytes.len()) % 4u64)) + to_integer((remainder.len() - at(tail_head, loop(5).iter.len()))); to_integer((old(bytes.len()) - old(bytes.len()) % 4u64)) + to_integer((remainder.len() - at(tail_head, loop(5).iter.len()))) == to_integer((old(bytes.len()) - at(tail_head, loop(5).iter.len()))); };
         rewrite(to_integer((old(bytes.len()) - at(tail_head, loop(5).iter.len()))), to_integer((old(bytes.len()) - old(bytes.len()) % 4u64) + (remainder.len() - at(tail_head, loop(5).iter.len()))));
         close() using { at(tail_head, loop(5).iter.as_slice()) == remainder.as_ptr() + (remainder.len() - at(tail_head, loop(5).iter.len())); remainder.as_ptr() + (remainder.len() - at(tail_head, loop(5).iter.len())) == bytes.as_ptr() + ((old(bytes.len()) - old(bytes.len()) % 4u64) + (remainder.len() - at(tail_head, loop(5).iter.len()))); };
        }
       step_until(loop(5).statement(0).entry);
       have to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len()) - 1u64);
       have to_integer(((loop(5).iter.len() as u32) as i32)) == to_integer(at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1) by { rewrite(to_integer(loop(5).iter.len()), to_integer(at(tail_head, loop(5).iter.len()) - 1u64)); close(); }
       have loop(5).iter.len() <= old(bytes.len()) by close() using { to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len()) - 1u64); 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= old(bytes.len()); };
       have to_integer(1u64) <= to_integer(old(bytes.len()) - loop(5).iter.len()) by close() using { to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len()) - 1u64); 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= old(bytes.len()); };
       have 0 <= ((loop(5).iter.len() as u32) as i32) by close() using { to_integer(((loop(5).iter.len() as u32) as i32)) == to_integer(at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1); 1 <= at(tail_head, ((loop(5).iter.len() as u32) as i32)); };
       have to_integer(old(bytes.len()) - loop(5).iter.len() - 1u64) == to_integer(old(bytes.len()) - at(tail_head, loop(5).iter.len())) by close() using { to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len()) - 1u64); 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= old(bytes.len()); };
       have at(tail_head, loop(5).iter.as_slice()) == bytes.as_ptr() + (old(bytes.len()) - loop(5).iter.len() - 1u64) by { rewrite(to_integer(old(bytes.len()) - loop(5).iter.len() - 1u64), to_integer(old(bytes.len()) - at(tail_head, loop(5).iter.len()))); close(); }
       have to_integer(old(bytes.len()) - loop(5).iter.len() - 1u64) <= to_integer(18446744073709551614u64) by close() using { to_integer(1u64) <= to_integer(old(bytes.len()) - loop(5).iter.len()); loop(5).iter.len() <= old(bytes.len()); };
       have to_integer((old(bytes.len()) - loop(5).iter.len() - 1u64)) <= to_integer(18446744073709551614u64);
       have to_integer(old(bytes.len()) - loop(5).iter.len() - 1u64) + 1 <= 18446744073709551615 by close() using { to_integer(old(bytes.len()) - loop(5).iter.len() - 1u64) <= to_integer(18446744073709551614u64); };
       have to_integer((old(bytes.len()) - loop(5).iter.len() - 1u64) + 1u64) == to_integer(old(bytes.len()) - loop(5).iter.len()) by close() using { to_integer(1u64) <= to_integer(old(bytes.len()) - loop(5).iter.len()); loop(5).iter.len() <= old(bytes.len()); };
       have (byte as u32) == (at(tail_head, loop(5).iter.as_slice()[0]) as u32);
       apply(adler_helper_byte_observation(at(tail_head, loop(5).iter.as_slice()[0])));
       have to_integer(byte as u32) == to_integer(((bytes.as_ptr() + (old(bytes.len()) - loop(5).iter.len() - 1u64))[0] as i32)) by { rewrite((byte as u32), (at(tail_head, loop(5).iter.as_slice()[0]) as u32)); rewrite(to_integer((at(tail_head, loop(5).iter.as_slice()[0]) as u32)), to_integer((at(tail_head, loop(5).iter.as_slice()[0]) as i32))); rewrite(at(tail_head, loop(5).iter.as_slice()), bytes.as_ptr() + (old(bytes.len()) - loop(5).iter.len() - 1u64)); close(); }
       have truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len() - 1u64, old(to_integer((self.a as u32)))) by { rewrite(to_integer(old(bytes.len()) - loop(5).iter.len() - 1u64), to_integer(old(bytes.len()) - at(tail_head, loop(5).iter.len()))); close(); }
       have truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len() - 1u64, old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(old(bytes.len()) - loop(5).iter.len() - 1u64), to_integer(old(bytes.len()) - at(tail_head, loop(5).iter.len()))); close(); }
       apply(adler_prefix_a_step_one_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len() - 1u64, old(to_integer((self.a as u32))), to_integer(a)));
       apply(adler_prefix_b_step_one_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len() - 1u64, old(to_integer((self.a as u32))), old(to_integer((self.b as u32))), to_integer(a), to_integer(b)));
       have (byte as u32) <= 255u32;
       have to_integer(byte as u32) <= to_integer(255u32);
       have to_integer(byte as u32) <= 255 by close() using { to_integer(byte as u32) <= to_integer(255u32); };
       apply(adler_tail_iterator_step(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32)), to_integer(a), to_integer(b), to_integer(byte as u32)));
       have a <= 4294967295u32 - (byte as u32) by close() using { to_integer(a) + to_integer(byte as u32) <= 4294967295; };
       mark tail_add_a;
       have to_integer(at(tail_add_a, a)) == to_integer(a) by close();
       have to_integer(at(tail_add_a, b)) == to_integer(b) by close();
       have to_integer(at(tail_add_a, byte as u32)) == to_integer(((bytes.as_ptr() + (old(bytes.len()) - loop(5).iter.len() - 1u64))[0] as i32)) by close() using { to_integer(byte as u32) == to_integer(((bytes.as_ptr() + (old(bytes.len()) - loop(5).iter.len() - 1u64))[0] as i32)); };
       have truncating_remainder(to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)), 65521) == adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len(), old(to_integer((self.a as u32)))) by {
        rewrite(to_integer(old(bytes.len()) - loop(5).iter.len()), to_integer((old(bytes.len()) - loop(5).iter.len() - 1u64) + 1u64));
        rewrite(to_integer(at(tail_add_a, a)), to_integer(a));
        rewrite(to_integer(at(tail_add_a, byte as u32)), to_integer(((bytes.as_ptr() + (old(bytes.len()) - loop(5).iter.len() - 1u64))[0] as i32)));
        close();
       }
       have truncating_remainder(to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)), 65521) == adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by {
        rewrite(to_integer(old(bytes.len()) - loop(5).iter.len()), to_integer((old(bytes.len()) - loop(5).iter.len() - 1u64) + 1u64));
        rewrite(to_integer(at(tail_add_a, b)), to_integer(b));
        rewrite(to_integer(at(tail_add_a, a)), to_integer(a));
        rewrite(to_integer(at(tail_add_a, byte as u32)), to_integer(((bytes.as_ptr() + (old(bytes.len()) - loop(5).iter.len() - 1u64))[0] as i32)));
        close();
       }

       have to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) <= 4294967295;
       step();
       have to_integer((at(tail_add_a, a) + at(tail_add_a, byte as u32))) == to_integer(at(tail_add_a, a) + at(tail_add_a, byte as u32));
       have to_integer(at(tail_add_a, a) + at(tail_add_a, byte as u32)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by apply(integer::uint32_add_to_integer(at(tail_add_a, a), at(tail_add_a, byte as u32)));
       have to_integer((at(tail_add_a, a) + at(tail_add_a, byte as u32))) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by { rewrite(to_integer((at(tail_add_a, a) + at(tail_add_a, byte as u32))), to_integer(at(tail_add_a, a) + at(tail_add_a, byte as u32))); close(); }
       have to_integer((at(tail_add_a, a) + at(tail_add_a, byte as u32))) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1) by close() using { to_integer(a) + to_integer(byte as u32) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1); to_integer((at(tail_add_a, a) + at(tail_add_a, byte as u32))) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)); };
       have to_integer(b) + to_integer((at(tail_add_a, a) + at(tail_add_a, byte as u32))) <= 4294967295 by close() using { to_integer(b) + to_integer(a) + to_integer(byte as u32) <= 4294967295; to_integer((at(tail_add_a, a) + at(tail_add_a, byte as u32))) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)); };
       have to_integer(b) + to_integer((at(tail_add_a, a) + at(tail_add_a, byte as u32))) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1) by close() using { to_integer(b) + to_integer(a) + to_integer(byte as u32) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1); to_integer((at(tail_add_a, a) + at(tail_add_a, byte as u32))) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)); };
       step_until(assignment(a, 2).entry); step();
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1);
       have a == (at(tail_add_a, a) + at(tail_add_a, byte as u32));
       have to_integer(a) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by { rewrite(a, (at(tail_add_a, a) + at(tail_add_a, byte as u32))); close(); }
       have truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len(), old(to_integer((self.a as u32)))) by { rewrite(to_integer(a), to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32))); close(); }
       have a == (at(tail_add_a, a) + at(tail_add_a, byte as u32));
       have to_integer(b) + to_integer(a) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1) by { rewrite(a, a); rewrite(a, (at(tail_add_a, a) + at(tail_add_a, byte as u32))); close(); }
       have to_integer(b) + to_integer(a) <= 4294967295;
       have b <= 4294967295u32 - a by close() using { to_integer(b) + to_integer(a) <= 4294967295; };
       mark tail_add_b;
       have to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b));
       have to_integer(at(tail_add_b, a)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32));

       have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, a)) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1) by close() using { to_integer(b) + to_integer(a) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1); };
       have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, a)) <= 4294967295;
       step();
       have to_integer((at(tail_add_b, b) + at(tail_add_b, a))) == to_integer(at(tail_add_b, b) + at(tail_add_b, a));
       have to_integer(at(tail_add_b, b) + at(tail_add_b, a)) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, a)) by apply(integer::uint32_add_to_integer(at(tail_add_b, b), at(tail_add_b, a)));

       have to_integer((at(tail_add_b, b) + at(tail_add_b, a))) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, a)) by { rewrite(to_integer((at(tail_add_b, b) + at(tail_add_b, a))), to_integer(at(tail_add_b, b) + at(tail_add_b, a))); close(); }
       have to_integer((at(tail_add_b, b) + at(tail_add_b, a))) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1) by { rewrite(to_integer((at(tail_add_b, b) + at(tail_add_b, a))), to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, a))); close(); }
       step_until(assignment(b, 6).entry); step();
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1);
       have to_integer(b) == to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by close() using { to_integer((at(tail_add_b, b) + at(tail_add_b, a))) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, a)); to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b)); to_integer(at(tail_add_b, a)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)); };
       have truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()) - loop(5).iter.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32))); close(); }
       step_until(loop.back_edge);
        have to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len()) - 1u64);
        have to_integer(((loop(5).iter.len() as u32) as i32)) == to_integer(at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1) by { rewrite(to_integer(loop(5).iter.len()), to_integer(at(tail_head, loop(5).iter.len()) - 1u64)); close(); }
       apply(adler_tail_remaining_progress(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))));
       have adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)) == adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1 by { rewrite(to_integer(((loop(5).iter.len() as u32) as i32)), to_integer(at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1)); close(); }
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)), adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1); close(); }
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)), adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1); close(); }
       have 0 <= to_integer(a); have to_integer(a) <= 4294967295; have 0 <= to_integer(b); have to_integer(b) <= 4294967295; 
       have 0 <= ((loop(5).iter.len() as u32) as i32) and ((loop(5).iter.len() as u32) as i32) <= ((remainder.len() as u32) as i32);
        have loop(5).iter.len() <= remainder.len() by close() using { to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len()) - 1u64); 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); };
        have to_integer(old(bytes.len()) - at(tail_head, loop(5).iter.len())) <= to_integer(18446744073709551614u64) by close() using { 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= old(bytes.len()); };
        have to_integer(old(bytes.len()) - loop(5).iter.len()) == to_integer((old(bytes.len()) - at(tail_head, loop(5).iter.len())) + 1u64) by close() using { to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len()) - 1u64); 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= old(bytes.len()); };
        have loop(5).iter.len() < at(tail_head, loop(5).iter.len()) by close() using { to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len()) - 1u64); 1u64 <= at(tail_head, loop(5).iter.len()); };
      }
     }

     step_until(statement(22).entry);
     have at(loop(5).exit, loop(5).iter.len()) == 0u64 by close() using { not (0u64 < at(loop(5).exit, loop(5).iter.len())); };
     have truncating_remainder(to_integer(at(loop(5).exit, a)), 65521) == adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()) - at(loop(5).exit, loop(5).iter.len()), old(to_integer((self.a as u32)))) by close();
     have to_integer(a) == to_integer(at(loop(5).exit, a)) by close();
     have to_integer(old(bytes.len())) == to_integer(old(bytes.len()) - at(loop(5).exit, loop(5).iter.len())) by { rewrite(at(loop(5).exit, loop(5).iter.len()), 0u64); close(); }
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32)))) by { rewrite(to_integer(a), to_integer(at(loop(5).exit, a))); rewrite(to_integer(old(bytes.len())), to_integer(old(bytes.len()) - at(loop(5).exit, loop(5).iter.len()))); close(); }
     have truncating_remainder(to_integer(at(loop(5).exit, b)), 65521) == adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()) - at(loop(5).exit, loop(5).iter.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by close();
     have to_integer(b) == to_integer(at(loop(5).exit, b)) by close();
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), to_integer(at(loop(5).exit, b))); rewrite(to_integer(old(bytes.len())), to_integer(old(bytes.len()) - at(loop(5).exit, loop(5).iter.len()))); close(); }
     have forall (k: uint64) { k < old(bytes.len()) implies bytes[k] == old(bytes[k]) } by close();
     apply(adler_spec_extensional_u64(bytes.as_ptr(), old(bytes.as_ptr()), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
     have adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32)))) == old(adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))))) by close() using { adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32)))) == adler_spec_a_u64(old(bytes.as_ptr()), old(bytes.len()), old(to_integer((self.a as u32)))); };
     have adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == old(adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by close() using { adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == adler_spec_b_u64(old(bytes.as_ptr()), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); };
     have truncating_remainder(to_integer(a), 65521) == old(adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))))) by close() using { truncating_remainder(to_integer(a), 65521) == adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32)))); adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32)))) == old(adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))))); };
     have truncating_remainder(to_integer(b), 65521) == old(adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by close() using { truncating_remainder(to_integer(b), 65521) == adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == old(adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };
     mark tail_done;
     have truncating_remainder(to_integer(at(tail_done, a)), 65521) == old(adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))))) by close() using { truncating_remainder(to_integer(a), 65521) == old(adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))))); };
     have truncating_remainder(to_integer(at(tail_done, b)), 65521) == old(adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by close() using { truncating_remainder(to_integer(b), 65521) == old(adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };

     apply(integer::uint32_remainder_to_integer(at(tail_done, a), 65521u32));
     have to_integer((at(tail_done, a) % 65521u32)) == truncating_remainder(to_integer(at(tail_done, a)), 65521) by close();
     have to_integer((at(tail_done, a) % 65521u32)) == old(adler_spec_a_u64(bytes.as_ptr(), bytes.len(), old(to_integer((self.a as u32))))) by { rewrite(to_integer((at(tail_done, a) % 65521u32)), truncating_remainder(to_integer(at(tail_done, a)), 65521)); close(); }
     have (at(tail_done, a) % 65521u32) < 65521u32;
     have 0 <= to_integer((at(tail_done, a) % 65521u32));
     have to_integer((at(tail_done, a) % 65521u32)) <= 4294967295;
     have to_integer((at(tail_done, a) % 65521u32)) < 65521 by close() using { to_integer((at(tail_done, a) % 65521u32)) < to_integer(65521u32); };
     have to_integer((at(tail_done, a) % 65521u32)) <= 65535 by close() using { to_integer((at(tail_done, a) % 65521u32)) < 65521; };
     apply(integer::uint32_remainder_to_integer(at(tail_done, b), 65521u32));
     have to_integer((at(tail_done, b) % 65521u32)) == truncating_remainder(to_integer(at(tail_done, b)), 65521) by close();
     have to_integer((at(tail_done, b) % 65521u32)) == old(adler_spec_b_u64(bytes.as_ptr(), bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by { rewrite(to_integer((at(tail_done, b) % 65521u32)), truncating_remainder(to_integer(at(tail_done, b)), 65521)); close(); }
     have (at(tail_done, b) % 65521u32) < 65521u32;
     have 0 <= to_integer((at(tail_done, b) % 65521u32));
     have to_integer((at(tail_done, b) % 65521u32)) <= 4294967295;
     have to_integer((at(tail_done, b) % 65521u32)) < 65521 by close() using { to_integer((at(tail_done, b) % 65521u32)) < to_integer(65521u32); };
     have to_integer((at(tail_done, b) % 65521u32)) <= 65535 by close() using { to_integer((at(tail_done, b) % 65521u32)) < 65521; };
     step_until(function.exit);
     have statement(22).call(0).result == 65521u32 by close();
     have self.a == ((at(tail_done, a) % statement(22).call(0).result) as u16) by close();
     have self.a == ((at(tail_done, a) % 65521u32) as u16) by { rewrite(self.a, ((at(tail_done, a) % statement(22).call(0).result) as u16)); rewrite(statement(22).call(0).result, 65521u32); close(); }
     have to_integer(self.a) == to_integer((at(tail_done, a) % 65521u32)) by { rewrite(self.a, ((at(tail_done, a) % 65521u32) as u16)); close() using { 0 <= to_integer((at(tail_done, a) % 65521u32)); to_integer((at(tail_done, a) % 65521u32)) <= 65535; }; }
     have to_integer(self.a) == old(adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))))) by { rewrite(to_integer(self.a), to_integer((at(tail_done, a) % 65521u32))); close(); }
     have to_integer((at(tail_done, a) % 65521u32)) < 65521;
     have to_integer(self.a) < 65521 by { rewrite(to_integer(self.a), to_integer((at(tail_done, a) % 65521u32))); close(); }
     have statement(23).call(0).result == 65521u32 by close();
     have self.b == ((at(tail_done, b) % statement(23).call(0).result) as u16) by close();
     have self.b == ((at(tail_done, b) % 65521u32) as u16) by { rewrite(self.b, ((at(tail_done, b) % statement(23).call(0).result) as u16)); rewrite(statement(23).call(0).result, 65521u32); close(); }
     have to_integer(self.b) == to_integer((at(tail_done, b) % 65521u32)) by { rewrite(self.b, ((at(tail_done, b) % 65521u32) as u16)); close() using { 0 <= to_integer((at(tail_done, b) % 65521u32)); to_integer((at(tail_done, b) % 65521u32)) <= 65535; }; }
     have to_integer(self.b) == old(adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by { rewrite(to_integer(self.b), to_integer((at(tail_done, b) % 65521u32))); close(); }
     have to_integer((at(tail_done, b) % 65521u32)) < 65521;
     have to_integer(self.b) < 65521 by { rewrite(to_integer(self.b), to_integer((at(tail_done, b) % 65521u32))); close(); }
     have 0 <= to_integer(self.a) by { rewrite(to_integer(self.a), to_integer((at(tail_done, a) % 65521u32))); close() using { 0 <= to_integer((at(tail_done, a) % 65521u32)); }; }
     have to_integer(self.a) <= 65535 by close() using { to_integer(self.a) < 65521; };
     have to_integer((self.a as i32)) == to_integer(self.a) by { close() using { 0 <= to_integer(self.a); to_integer(self.a) <= 65535; }; }
     have to_integer((self.a as i32)) <= to_integer(65520) by { rewrite(to_integer((self.a as i32)), to_integer(self.a)); close() using { to_integer(self.a) < 65521; }; }
     have ((self.a as i32)) <= 65520;
     apply(adler_i32_below_mod((self.a as i32)));
     have self.a < 65521 by close();
     have 0 <= to_integer(self.b) by { rewrite(to_integer(self.b), to_integer((at(tail_done, b) % 65521u32))); close() using { 0 <= to_integer((at(tail_done, b) % 65521u32)); }; }
     have to_integer(self.b) <= 65535 by close() using { to_integer(self.b) < 65521; };
     have to_integer((self.b as i32)) == to_integer(self.b) by { close() using { 0 <= to_integer(self.b); to_integer(self.b) <= 65535; }; }
     have to_integer((self.b as i32)) <= to_integer(65520) by { rewrite(to_integer((self.b as i32)), to_integer(self.b)); close() using { to_integer(self.b) < 65521; }; }
     have ((self.b as i32)) <= 65520;
     apply(adler_i32_below_mod((self.b as i32)));
     have self.b < 65521 by close();
     have to_integer(self.a) <= 65520 by close() using { to_integer(self.a) < 65521; };
     have to_integer(self.b) <= 65520 by close() using { to_integer(self.b) < 65521; };
     close() using { self.a < 65521; self.b < 65521; to_integer(self.a) <= 65520; to_integer(self.b) <= 65520; to_integer(self.a) == old(adler_spec_a_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))))); to_integer(self.b) == old(adler_spec_b_u64(bytes.as_ptr(), old(bytes.len()), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };
    }
}
