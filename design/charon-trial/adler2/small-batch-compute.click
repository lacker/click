# Original compute bounds for every small-batch length and canonical seeds.
# Length is at most 22207 bytes; both initial fields are below MOD = 65521.
# The stored vector and scalar iterators supply their actual remaining state.
# Full outer batches and final checksum postconditions remain separate work.
# Verification assembles this contract with checked helpers and arithmetic libraries.

theorem adler_uint64_self_subtract(n: uint64) { ensures n - n == 0u64 by { normalize(); } }
theorem adler_i32_below_mod(n: int32) { requires n <= 65520; ensures n < 65521 by { arithmetic() using { n <= 65520; } } }
theorem adler_bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22200;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by { simp() using { 0 <= index; index <= 22200; } }
  normalize() using { defined(index + 4); }
 }
}
theorem adler_scalar_batch_product_bound(length: uint32, seed: uint32) {
 requires length <= 22204u32;
 requires seed <= 65520u32;
 ensures to_integer(length) * to_integer(seed) <= 1454806080 by {
  apply(uint32_to_integer_bounds(length));
  apply(uint32_to_integer_bounds(seed));
  apply(uint32_less_equal_to_integer(length, 22204u32)) using { length <= 22204u32; }
  apply(uint32_less_equal_to_integer(seed, 65520u32)) using { seed <= 65520u32; }
  arithmetic_certificate special {
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
 ensures (uint32)length <= 22204u32 and to_integer((uint32)length) == to_integer(length) by {
  have 0u64 <= length by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, length)) using { 0u64 <= length; }
  apply(uint64_less_equal_to_integer(length, 22204u64)) using { length <= 22204u64; }
  have 0 <= to_integer(length) by { assumption(); }
  have to_integer(length) <= 4294967295 by { arithmetic() using { to_integer(length) <= 22204; } }
  have to_integer((uint32)length) == to_integer(length) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(length) => 0 <= to_integer(length);
    premise 1: to_integer(length) <= 4294967295 => to_integer(length) <= 4294967295;
    integer_cast_identity bounds [0, 1] => to_integer((uint32)length) == to_integer(length);
    conclusion 0;
   }
  }
  have to_integer((uint32)length) <= to_integer(22204u32) by { rewrite(to_integer((uint32)length) == to_integer(length)); assumption(); }
  apply(uint32_less_equal_of_to_integer((uint32)length, 22204u32)) using { to_integer((uint32)length) <= to_integer(22204u32); }
  simp();
 }
}



theorem adler_tail_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22206;
 ensures (base + index) + 1 == base + (index + 1) by {
  have defined(index + 1) by { simp() using { 0 <= index; index <= 22206; } }
  normalize() using { defined(index + 1); }
 }
}

void __rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute(struct __rust_q_I6_adler2_I7_Adler32* self, const uint8* bytes, uint64 bytes_len) {
 requires bytes_len <= 22207u64;
 requires bytes_len < 22208u64;
 requires (uint32)self->a <= 65520u32;
 requires (uint32)self->b <= 65520u32;
 owns self->a;
 owns self->b;
 views bytes[0..bytes_len];
 ensures self->a < 65521;
 ensures self->b < 65521;
} by {
 apply(adler_signed_small_prefix(bytes_len)) using { bytes_len <= 22207u64; }
 apply(adler_small_prefix_divisible(bytes_len)) using { bytes_len <= 22207u64; }
 apply(adler_native_small_prefix_divisible(bytes_len)) using { bytes_len <= 22207u64; }
 apply(adler_small_native_prefix(bytes_len)) using { bytes_len <= 22207u64; }
 apply(adler_small_tail_metadata(bytes_len)) using { bytes_len <= 22207u64; }
 apply(adler_small_signed_tail(bytes_len)) using { bytes_len <= 22207u64; }
 apply(adler_signed_partition_identity(bytes_len)) using { bytes_len <= 22207u64; }
 have bytes_len % 4u64 <= bytes_len by { normalize(); }
 have bytes_len - bytes_len % 4u64 <= bytes_len by { normalize() using { bytes_len % 4u64 <= bytes_len; } }
 apply(adler_small_outer_remainder(bytes_len - bytes_len % 4u64)) using { bytes_len - bytes_len % 4u64 <= 22204u64; }
 have bytes_len <= 2147483647u64 by { normalize() using { bytes_len <= 22207u64; } }
 have 0 <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { simp() using { 0 <= (int32)(uint32)(bytes_len - bytes_len % 4u64); } }
 have old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204 by { simp() using { (int32)(uint32)(bytes_len - bytes_len % 4u64) <= 22204; } }
 have old((int32)(uint32)(bytes_len - bytes_len % 4u64)) % 4 == 0 by { simp() using { (int32)(uint32)(bytes_len - bytes_len % 4u64) % 4 == 0; } }
 have bytes_len % 4u64 <= bytes_len by { normalize(); }
 have bytes_len - bytes_len % 4u64 <= bytes_len by { normalize() using { bytes_len % 4u64 <= bytes_len; } }
 have bytes_len - bytes_len % 4u64 <= 2147483647u64 by { normalize() using { bytes_len - bytes_len % 4u64 <= bytes_len; bytes_len <= 2147483647u64; } }
 apply(uint64_less_equal_to_integer(bytes_len, 22207u64)) using { bytes_len <= 22207u64; }
 have bytes_len < 22208u64 by { assumption(); }
 execute_until(assignment(b, 0)); step();
 have a == old((uint32)self->a) by { simp(); }
 have a <= 65520u32 by { rewrite(a == old((uint32)self->a)); assumption(); }
 have b == old((uint32)self->b) by { simp(); }
 have b <= 65520u32 by { rewrite(b == old((uint32)self->b)); assumption(); }
 execute_until(assignment(remainder_chunk_len, 0)); step();
 have (int32)(uint32)remainder_chunk_len == old((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { simp(); }
 execute_until(loop(0));
 have __rust_mir_27_size == 22208u64 by { simp(); }
 have __rust_mir_10_len == bytes_len - bytes_len % 4u64 by { simp(); }
 have __rust_mir_27_remaining == __rust_mir_10_len - __rust_mir_10_len % 22208u64 by { simp(); }
 have __rust_mir_27_remaining == 0u64 by { rewrite(__rust_mir_27_remaining == __rust_mir_10_len - __rust_mir_10_len % 22208u64); rewrite(__rust_mir_10_len == bytes_len - bytes_len % 4u64); rewrite((bytes_len - bytes_len % 4u64) % 22208u64 == bytes_len - bytes_len % 4u64); apply(adler_uint64_self_subtract(bytes_len - bytes_len % 4u64)); simp(); }
 have remainder_chunk_len == bytes_len - bytes_len % 4u64 by { simp(); }
 apply(uint64_less_equal_to_integer(bytes_len, 2147483647u64)) using { bytes_len <= 2147483647u64; }
 have to_integer(remainder_chunk_len) == to_integer(bytes_len - bytes_len % 4u64) by { rewrite(remainder_chunk_len == bytes_len - bytes_len % 4u64); normalize(); }
 apply(uint64_less_equal_to_integer(bytes_len - bytes_len % 4u64, 2147483647u64)) using { bytes_len - bytes_len % 4u64 <= 2147483647u64; }
 have to_integer(remainder_chunk_len) <= to_integer(2147483647u64) by { rewrite(to_integer(remainder_chunk_len) == to_integer(bytes_len - bytes_len % 4u64)); assumption(); }
 apply(uint64_less_equal_of_to_integer(remainder_chunk_len, 2147483647u64)) using { to_integer(remainder_chunk_len) <= to_integer(2147483647u64); }
 execute_until(loop(2));
 have __rust_mir_62_remaining == bytes_len - bytes_len % 4u64 by { simp(); }
 have (int32)(uint32)__rust_mir_62_remaining == old((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { rewrite(__rust_mir_62_remaining == bytes_len - bytes_len % 4u64); simp(); }
 have __rust_mir_62_cursor == bytes + __rust_mir_27_remaining by { normalize(); }
 have __rust_mir_62_cursor == bytes by { rewrite(__rust_mir_62_cursor == bytes + __rust_mir_27_remaining); rewrite(__rust_mir_27_remaining == 0u64); normalize(); }
 have bytes == old(bytes) by { simp(); }
 have __rust_mir_62_cursor == old(bytes) by { rewrite(__rust_mir_62_cursor == bytes); assumption(); }
 have __rust_mir_62_size == 4u64 by { simp(); }
 apply(adler_lane_initial_ceiling());
 apply(adler_lane_iterator_initial(old((int32)(uint32)(bytes_len - bytes_len % 4u64))));
 have adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining) == 0 by { rewrite((int32)(uint32)__rust_mir_62_remaining == old((int32)(uint32)(bytes_len - bytes_len % 4u64))); assumption(); }
 have to_integer(a_vec._0[0]) == 0 by { simp(); }
 have to_integer(a_vec._0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec._0[0]) == 0; } }
 have to_integer(b_vec._0[0]) == 0 by { simp(); }
 have to_integer(b_vec._0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec._0[0]) == 0; } }
 have to_integer(a_vec._0[1]) == 0 by { simp(); }
 have to_integer(a_vec._0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec._0[1]) == 0; } }
 have to_integer(b_vec._0[1]) == 0 by { simp(); }
 have to_integer(b_vec._0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec._0[1]) == 0; } }
 have to_integer(a_vec._0[2]) == 0 by { simp(); }
 have to_integer(a_vec._0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec._0[2]) == 0; } }
 have to_integer(b_vec._0[2]) == 0 by { simp(); }
 have to_integer(b_vec._0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec._0[2]) == 0; } }
 have to_integer(a_vec._0[3]) == 0 by { simp(); }
 have to_integer(a_vec._0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec._0[3]) == 0; } }
 have to_integer(b_vec._0[3]) == 0 by { simp(); }
 have to_integer(b_vec._0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec._0[3]) == 0; } }
 have 0 <= (int32)(uint32)__rust_mir_62_remaining by { rewrite((int32)(uint32)__rust_mir_62_remaining == old((int32)(uint32)(bytes_len - bytes_len % 4u64))); assumption(); }
 have (int32)(uint32)__rust_mir_62_remaining <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { rewrite((int32)(uint32)__rust_mir_62_remaining == old((int32)(uint32)(bytes_len - bytes_len % 4u64))); normalize() using {}; }
 have 0 <= (int32)(uint32)__rust_mir_62_remaining and (int32)(uint32)__rust_mir_62_remaining <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { assumption(); }
 have (int32)(uint32)__rust_mir_62_remaining % 4 == 0 by { rewrite((int32)(uint32)__rust_mir_62_remaining == old((int32)(uint32)(bytes_len - bytes_len % 4u64))); assumption(); }
 have __rust_mir_62_remaining <= bytes_len - bytes_len % 4u64 by { rewrite(__rust_mir_62_remaining == bytes_len - bytes_len % 4u64); normalize(); }
 have __rust_mir_62_remaining % 4u64 == 0u64 by { rewrite(__rust_mir_62_remaining == bytes_len - bytes_len % 4u64); simp(); }
 have (bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining == 0u64 by { rewrite(__rust_mir_62_remaining == bytes_len - bytes_len % 4u64); apply(adler_uint64_self_subtract(bytes_len - bytes_len % 4u64)); }
 have __rust_mir_62_cursor == bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining) by { rewrite((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining == 0u64); rewrite(__rust_mir_62_cursor == bytes); normalize(); }
 have bytes_len < 22208u64 by { assumption(); }
 have bytes_len == old(bytes_len) by { assumption(); }
 apply(uint32_to_integer_bounds(a)) using {};
 apply(uint32_less_equal_to_integer(a, 65520u32)) using { a <= 65520u32; }
 apply(adler_spec_empty(bytes, to_integer(a), 0)) using { 0 <= to_integer(a); to_integer(a) <= 65520; 0 <= 0; 0 <= 65520; }
 have ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) == 0 by { rewrite((int32)(uint32)__rust_mir_62_remaining == (int32)(uint32)(bytes_len - bytes_len % 4u64)); normalize(); }
 have adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3])) == to_integer(a) by { unfold(adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]))); arithmetic() using { to_integer(a_vec._0[0]) == 0; to_integer(a_vec._0[1]) == 0; to_integer(a_vec._0[2]) == 0; to_integer(a_vec._0[3]) == 0; } }
 have to_integer(a) == 0 * 65521 + to_integer(a) by { arithmetic() using {}; }
 apply(adler_residue_unique(to_integer(a), 0, to_integer(a))) using { 0 <= to_integer(a); to_integer(a) == 0 * 65521 + to_integer(a); to_integer(a) <= 65520; };
 have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3])), 65521) == adler_spec_a(bytes, ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining), to_integer(a)) by { rewrite(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) == 0); rewrite(adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3])) == to_integer(a)); arithmetic() using { truncating_remainder(to_integer(a), 65521) == to_integer(a); adler_spec_a(bytes, 0, to_integer(a)) == to_integer(a); } }
 apply(uint32_to_integer_bounds(b)) using {};
 apply(uint32_less_equal_to_integer(b, 65520u32)) using { b <= 65520u32; }
 apply(adler_spec_empty(bytes, to_integer(a), to_integer(b))) using { 0 <= to_integer(a); to_integer(a) <= 65520; 0 <= to_integer(b); to_integer(b) <= 65520; }
 have to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) == 0 by { simp() using { ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) == 0; } }
 have adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) == to_integer(b) + 393126 by { rewrite(to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) == 0); unfold(adler_lane_b(to_integer(b) + 0 * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3]))); arithmetic() using { to_integer(a_vec._0[1]) == 0; to_integer(a_vec._0[2]) == 0; to_integer(a_vec._0[3]) == 0; to_integer(b_vec._0[0]) == 0; to_integer(b_vec._0[1]) == 0; to_integer(b_vec._0[2]) == 0; to_integer(b_vec._0[3]) == 0; } }
 have 0 <= to_integer(b) + 393126 by { arithmetic() using { 0 <= to_integer(b); } }
 have 0 <= adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) == to_integer(b) + 393126); assumption(); }
 have to_integer(b) + 393126 == 6 * 65521 + to_integer(b) by { arithmetic() using {}; }
 apply(adler_residue_unique(to_integer(b) + 393126, 6, to_integer(b))) using { 0 <= to_integer(b) + 393126; to_integer(b) + 393126 == 6 * 65521 + to_integer(b); 0 <= to_integer(b); to_integer(b) <= 65520; };
 have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])), 65521) == adler_spec_b(bytes, ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining), to_integer(a), to_integer(b)) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) == to_integer(b) + 393126); rewrite(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) == 0); arithmetic() using { truncating_remainder(to_integer(b) + 393126, 65521) == to_integer(b); adler_spec_b(bytes, 0, to_integer(a), to_integer(b)) == to_integer(b); } }
 loop {
  decreases __rust_mir_62_remaining;
  owns a_vec._0[0..4];
  owns b_vec._0[0..4];
  views bytes[0..bytes_len];
  invariant bytes_len <= 22207u64;
  invariant bytes_len < 22208u64;
  invariant bytes_len - bytes_len % 4u64 <= 22204u64;
  invariant bytes == old(bytes);
  invariant bytes_len == old(bytes_len);
  invariant a <= 65520u32;
  invariant b <= 65520u32;
  invariant 0 <= old((int32)(uint32)(bytes_len - bytes_len % 4u64));
  invariant old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204;
  invariant old((int32)(uint32)(bytes_len - bytes_len % 4u64)) % 4 == 0;
  invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3])), 65521) == adler_spec_a(bytes, ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining), to_integer(a));
  invariant 0 <= adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3]));
  invariant truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])), 65521) == adler_spec_b(bytes, ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining), to_integer(a), to_integer(b));
  invariant __rust_mir_62_size == 4u64;
  invariant 0 <= (int32)(uint32)__rust_mir_62_remaining and (int32)(uint32)__rust_mir_62_remaining <= old((int32)(uint32)(bytes_len - bytes_len % 4u64));
  invariant (int32)(uint32)__rust_mir_62_remaining % 4 == 0;
  invariant __rust_mir_62_remaining <= bytes_len - bytes_len % 4u64;
  invariant __rust_mir_62_remaining % 4u64 == 0u64;
  invariant __rust_mir_62_cursor == bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining);
  invariant to_integer(a_vec._0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining));
  invariant to_integer(b_vec._0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining));
  invariant to_integer(a_vec._0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining));
  invariant to_integer(b_vec._0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining));
  invariant to_integer(a_vec._0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining));
  invariant to_integer(b_vec._0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining));
  invariant to_integer(a_vec._0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining));
  invariant to_integer(b_vec._0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining));
  preserve by {
   have 4u64 <= __rust_mir_62_remaining by { simp(); }
   have __rust_mir_62_remaining <= 22208u64 by { arithmetic() using { __rust_mir_62_remaining <= bytes_len - bytes_len % 4u64; bytes_len - bytes_len % 4u64 <= 22204u64; } }
   apply(adler_count_lane_step(__rust_mir_62_remaining)) using { 4u64 <= __rust_mir_62_remaining; __rust_mir_62_remaining <= 22208u64; }
   mark lane_head;
   have at(lane_head, (int32)(uint32)__rust_mir_62_remaining) % 4 == 0 by { simp(); }
   have at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { simp(); }
   have 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining) by { simp(); }
   have 0 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining) by { simp(); }
   have old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22208 by { arithmetic() using { old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; } }
   have 4u64 <= at(lane_head, __rust_mir_62_remaining) by { simp(); }
   have at(lane_head, __rust_mir_62_remaining) <= bytes_len - bytes_len % 4u64 by { simp(); }
   have bytes_len - bytes_len % 4u64 <= bytes_len by { normalize(); }
   have at(lane_head, __rust_mir_62_cursor) == bytes + ((bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining)) by { simp(); }
   have (bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining) <= bytes_len by { arithmetic() using { at(lane_head, __rust_mir_62_remaining) <= bytes_len - bytes_len % 4u64; bytes_len - bytes_len % 4u64 <= bytes_len; } }
   have 4u64 <= bytes_len - ((bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining)) by { arithmetic() using { 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= bytes_len - bytes_len % 4u64; bytes_len - bytes_len % 4u64 <= bytes_len; } }
   have 0 <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining) by { arithmetic() using { 0 <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; 0 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); } }
   have (old((int32)(uint32)(bytes_len - bytes_len % 4u64)) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining)) + 4 <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { arithmetic() using { 0 <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); } }
   execute_until(assignment(__rust_mir_69, 0)); step();
   have __rust_mir_69 == at(lane_head, __rust_mir_62_cursor) by { simp(); }
   execute_until(assignment(__rust_mir_69_len, 0)); step();
   have __rust_mir_69_len == 4u64 by { simp(); }
   have __rust_mir_69 == bytes + ((bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining)) by { rewrite(__rust_mir_69 == at(lane_head, __rust_mir_62_cursor)); assumption(); }
   have __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64 by { simp(); }
   have (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4 by { rewrite(__rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64); simp(); }
   apply(adler_signed_small_prefix(bytes_len)) using { bytes_len <= 22207u64; }
   apply(adler_small_signed_tail(bytes_len)) using { bytes_len <= 22207u64; }
   apply(adler_signed_partition_identity(bytes_len)) using { bytes_len <= 22207u64; }
   have (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { simp() using { bytes_len == old(bytes_len); } }
   apply(adler_small_prefix_within_full(bytes_len)) using { bytes_len <= 22207u64; }
   have 0 <= (int32)(uint32)bytes_len by { assumption(); }
   have (int32)(uint32)bytes_len <= 22207 by { assumption(); }
   have old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= (int32)(uint32)bytes_len by { simp() using { (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)); (int32)(uint32)(bytes_len - bytes_len % 4u64) <= (int32)(uint32)bytes_len; } }
   have __rust_mir_62_remaining <= (bytes_len - bytes_len % 4u64) by { arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= (bytes_len - bytes_len % 4u64); } }
   have 4u64 <= (bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining by { arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= (bytes_len - bytes_len % 4u64); } }
   have (bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining) == (bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64 by { arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= (bytes_len - bytes_len % 4u64); } }
   have __rust_mir_69 == bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64) by { rewrite(__rust_mir_69 == bytes + ((bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining))); rewrite((bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining) == (bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64); normalize(); }
   have 0 <= (int32)(uint32)__rust_mir_62_remaining by { arithmetic() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; } }
   have (int32)(uint32)__rust_mir_62_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64) by { arithmetic() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)); } }
   have 4 <= (int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining by { arithmetic() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)); } }
   have (int32)(uint32)(bytes_len - bytes_len % 4u64) <= 22204 by { normalize() using { (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; } }
   execute_until(assignment(__rust_mir_71, 0));
   mark vector_a;
   have at(vector_a, __rust_mir_68._0[0]) == at(vector_a, (uint32)__rust_mir_69[0]) by { normalize() using { __rust_mir_68._0[0] == at(vector_a, (uint32)__rust_mir_69[0]); } }
   apply(adler_helper_byte_observation(at(vector_a, __rust_mir_69[0]))) using {};
   have to_integer(at(vector_a, __rust_mir_68._0[0])) == at(vector_a, to_integer((int32)__rust_mir_69[0])) by {
    rewrite(at(vector_a, __rust_mir_68._0[0]) == at(vector_a, (uint32)__rust_mir_69[0]));
    normalize() using { at(vector_a, to_integer((uint32)__rust_mir_69[0])) == at(vector_a, to_integer((int32)__rust_mir_69[0])); }
   }
   have at(vector_a, __rust_mir_68._0[1]) == at(vector_a, (uint32)__rust_mir_69[1]) by { normalize() using { __rust_mir_68._0[1] == at(vector_a, (uint32)__rust_mir_69[1]); } }
   apply(adler_helper_byte_observation(at(vector_a, __rust_mir_69[1]))) using {};
   have to_integer(at(vector_a, __rust_mir_68._0[1])) == at(vector_a, to_integer((int32)__rust_mir_69[1])) by {
    rewrite(at(vector_a, __rust_mir_68._0[1]) == at(vector_a, (uint32)__rust_mir_69[1]));
    normalize() using { at(vector_a, to_integer((uint32)__rust_mir_69[1])) == at(vector_a, to_integer((int32)__rust_mir_69[1])); }
   }
   have at(vector_a, __rust_mir_68._0[2]) == at(vector_a, (uint32)__rust_mir_69[2]) by { normalize() using { __rust_mir_68._0[2] == at(vector_a, (uint32)__rust_mir_69[2]); } }
   apply(adler_helper_byte_observation(at(vector_a, __rust_mir_69[2]))) using {};
   have to_integer(at(vector_a, __rust_mir_68._0[2])) == at(vector_a, to_integer((int32)__rust_mir_69[2])) by {
    rewrite(at(vector_a, __rust_mir_68._0[2]) == at(vector_a, (uint32)__rust_mir_69[2]));
    normalize() using { at(vector_a, to_integer((uint32)__rust_mir_69[2])) == at(vector_a, to_integer((int32)__rust_mir_69[2])); }
   }
   have at(vector_a, __rust_mir_68._0[3]) == at(vector_a, (uint32)__rust_mir_69[3]) by { normalize() using { __rust_mir_68._0[3] == at(vector_a, (uint32)__rust_mir_69[3]); } }
   apply(adler_helper_byte_observation(at(vector_a, __rust_mir_69[3]))) using {};
   have to_integer(at(vector_a, __rust_mir_68._0[3])) == at(vector_a, to_integer((int32)__rust_mir_69[3])) by {
    rewrite(at(vector_a, __rust_mir_68._0[3]) == at(vector_a, (uint32)__rust_mir_69[3]));
    normalize() using { at(vector_a, to_integer((uint32)__rust_mir_69[3])) == at(vector_a, to_integer((int32)__rust_mir_69[3])); }
   }
   apply(adler_count_previous_chunk_byte_observation(bytes, (bytes_len - bytes_len % 4u64), __rust_mir_62_remaining, 0)) using { __rust_mir_62_remaining <= (bytes_len - bytes_len % 4u64); 4u64 <= (bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining; (bytes_len - bytes_len % 4u64) <= 22204u64; 0 <= (int32)(uint32)__rust_mir_62_remaining; (int32)(uint32)__rust_mir_62_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64); (int32)(uint32)(bytes_len - bytes_len % 4u64) <= 22204; 0 <= 0; 0 <= 3; }
   have at(vector_a, __rust_mir_69[0]) == (bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[0] by { simp() using { __rust_mir_69 == bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64); } }
   have at(vector_a, to_integer((int32)__rust_mir_69[0])) == to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[0]) by { rewrite(at(vector_a, __rust_mir_69[0]) == (bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[0]); normalize(); }
   have to_integer(at(vector_a, __rust_mir_68._0[0])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 0]) by { arithmetic() using { to_integer(at(vector_a, __rust_mir_68._0[0])) == at(vector_a, to_integer((int32)__rust_mir_69[0])); at(vector_a, to_integer((int32)__rust_mir_69[0])) == to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[0]); to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[0]) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 0]); } }
   apply(adler_count_previous_chunk_byte_observation(bytes, (bytes_len - bytes_len % 4u64), __rust_mir_62_remaining, 1)) using { __rust_mir_62_remaining <= (bytes_len - bytes_len % 4u64); 4u64 <= (bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining; (bytes_len - bytes_len % 4u64) <= 22204u64; 0 <= (int32)(uint32)__rust_mir_62_remaining; (int32)(uint32)__rust_mir_62_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64); (int32)(uint32)(bytes_len - bytes_len % 4u64) <= 22204; 0 <= 1; 1 <= 3; }
   have at(vector_a, __rust_mir_69[1]) == (bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[1] by { simp() using { __rust_mir_69 == bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64); } }
   have at(vector_a, to_integer((int32)__rust_mir_69[1])) == to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[1]) by { rewrite(at(vector_a, __rust_mir_69[1]) == (bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[1]); normalize(); }
   have to_integer(at(vector_a, __rust_mir_68._0[1])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]) by { arithmetic() using { to_integer(at(vector_a, __rust_mir_68._0[1])) == at(vector_a, to_integer((int32)__rust_mir_69[1])); at(vector_a, to_integer((int32)__rust_mir_69[1])) == to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[1]); to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[1]) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]); } }
   apply(adler_count_previous_chunk_byte_observation(bytes, (bytes_len - bytes_len % 4u64), __rust_mir_62_remaining, 2)) using { __rust_mir_62_remaining <= (bytes_len - bytes_len % 4u64); 4u64 <= (bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining; (bytes_len - bytes_len % 4u64) <= 22204u64; 0 <= (int32)(uint32)__rust_mir_62_remaining; (int32)(uint32)__rust_mir_62_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64); (int32)(uint32)(bytes_len - bytes_len % 4u64) <= 22204; 0 <= 2; 2 <= 3; }
   have at(vector_a, __rust_mir_69[2]) == (bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[2] by { simp() using { __rust_mir_69 == bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64); } }
   have at(vector_a, to_integer((int32)__rust_mir_69[2])) == to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[2]) by { rewrite(at(vector_a, __rust_mir_69[2]) == (bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[2]); normalize(); }
   have to_integer(at(vector_a, __rust_mir_68._0[2])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]) by { arithmetic() using { to_integer(at(vector_a, __rust_mir_68._0[2])) == at(vector_a, to_integer((int32)__rust_mir_69[2])); at(vector_a, to_integer((int32)__rust_mir_69[2])) == to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[2]); to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[2]) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]); } }
   apply(adler_count_previous_chunk_byte_observation(bytes, (bytes_len - bytes_len % 4u64), __rust_mir_62_remaining, 3)) using { __rust_mir_62_remaining <= (bytes_len - bytes_len % 4u64); 4u64 <= (bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining; (bytes_len - bytes_len % 4u64) <= 22204u64; 0 <= (int32)(uint32)__rust_mir_62_remaining; (int32)(uint32)__rust_mir_62_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64); (int32)(uint32)(bytes_len - bytes_len % 4u64) <= 22204; 0 <= 3; 3 <= 3; }
   have at(vector_a, __rust_mir_69[3]) == (bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[3] by { simp() using { __rust_mir_69 == bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64); } }
   have at(vector_a, to_integer((int32)__rust_mir_69[3])) == to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[3]) by { rewrite(at(vector_a, __rust_mir_69[3]) == (bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[3]); normalize(); }
   have to_integer(at(vector_a, __rust_mir_68._0[3])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3]) by { arithmetic() using { to_integer(at(vector_a, __rust_mir_68._0[3])) == at(vector_a, to_integer((int32)__rust_mir_69[3])); at(vector_a, to_integer((int32)__rust_mir_69[3])) == to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[3]); to_integer((int32)(bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining - 4u64))[3]) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3]); } }
   apply(uint32_to_integer_bounds(at(vector_a, a_vec._0[0])));
   apply(uint32_to_integer_bounds(at(vector_a, b_vec._0[0])));
   apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68._0[0])));
   have 0 <= to_integer(at(vector_a, a_vec._0[0])) by { simp(); }
   have 0 <= to_integer(at(vector_a, b_vec._0[0])) by { simp(); }
   have to_integer(at(vector_a, a_vec._0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))) by { simp(); }
   have to_integer(at(vector_a, b_vec._0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))) by { simp(); }
   have 0 <= to_integer(at(vector_a, __rust_mir_68._0[0])) by { simp(); }
   have to_integer(at(vector_a, __rust_mir_68._0[0])) <= 255 by { simp(); }
   apply(adler_lane_iterator_add_contracts(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining), at(vector_a, a_vec._0[0]), at(vector_a, b_vec._0[0]), at(vector_a, __rust_mir_68._0[0]))) using { 0 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[0])); to_integer(at(vector_a, a_vec._0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[0])); to_integer(at(vector_a, b_vec._0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[0])); to_integer(at(vector_a, __rust_mir_68._0[0])) <= 255; }
   apply(adler_lane_iterator_native_preservation(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining), at(vector_a, a_vec._0[0]), at(vector_a, b_vec._0[0]), at(vector_a, __rust_mir_68._0[0]))) using { 0 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[0])); to_integer(at(vector_a, a_vec._0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[0])); to_integer(at(vector_a, b_vec._0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[0])); to_integer(at(vector_a, __rust_mir_68._0[0])) <= 255; }
   apply(uint32_to_integer_bounds(at(vector_a, a_vec._0[1])));
   apply(uint32_to_integer_bounds(at(vector_a, b_vec._0[1])));
   apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68._0[1])));
   have 0 <= to_integer(at(vector_a, a_vec._0[1])) by { simp(); }
   have 0 <= to_integer(at(vector_a, b_vec._0[1])) by { simp(); }
   have to_integer(at(vector_a, a_vec._0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))) by { simp(); }
   have to_integer(at(vector_a, b_vec._0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))) by { simp(); }
   have 0 <= to_integer(at(vector_a, __rust_mir_68._0[1])) by { simp(); }
   have to_integer(at(vector_a, __rust_mir_68._0[1])) <= 255 by { simp(); }
   apply(adler_lane_iterator_add_contracts(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining), at(vector_a, a_vec._0[1]), at(vector_a, b_vec._0[1]), at(vector_a, __rust_mir_68._0[1]))) using { 0 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[1])); to_integer(at(vector_a, a_vec._0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[1])); to_integer(at(vector_a, b_vec._0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[1])); to_integer(at(vector_a, __rust_mir_68._0[1])) <= 255; }
   apply(adler_lane_iterator_native_preservation(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining), at(vector_a, a_vec._0[1]), at(vector_a, b_vec._0[1]), at(vector_a, __rust_mir_68._0[1]))) using { 0 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[1])); to_integer(at(vector_a, a_vec._0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[1])); to_integer(at(vector_a, b_vec._0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[1])); to_integer(at(vector_a, __rust_mir_68._0[1])) <= 255; }
   apply(uint32_to_integer_bounds(at(vector_a, a_vec._0[2])));
   apply(uint32_to_integer_bounds(at(vector_a, b_vec._0[2])));
   apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68._0[2])));
   have 0 <= to_integer(at(vector_a, a_vec._0[2])) by { simp(); }
   have 0 <= to_integer(at(vector_a, b_vec._0[2])) by { simp(); }
   have to_integer(at(vector_a, a_vec._0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))) by { simp(); }
   have to_integer(at(vector_a, b_vec._0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))) by { simp(); }
   have 0 <= to_integer(at(vector_a, __rust_mir_68._0[2])) by { simp(); }
   have to_integer(at(vector_a, __rust_mir_68._0[2])) <= 255 by { simp(); }
   apply(adler_lane_iterator_add_contracts(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining), at(vector_a, a_vec._0[2]), at(vector_a, b_vec._0[2]), at(vector_a, __rust_mir_68._0[2]))) using { 0 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[2])); to_integer(at(vector_a, a_vec._0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[2])); to_integer(at(vector_a, b_vec._0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[2])); to_integer(at(vector_a, __rust_mir_68._0[2])) <= 255; }
   apply(adler_lane_iterator_native_preservation(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining), at(vector_a, a_vec._0[2]), at(vector_a, b_vec._0[2]), at(vector_a, __rust_mir_68._0[2]))) using { 0 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[2])); to_integer(at(vector_a, a_vec._0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[2])); to_integer(at(vector_a, b_vec._0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[2])); to_integer(at(vector_a, __rust_mir_68._0[2])) <= 255; }
   apply(uint32_to_integer_bounds(at(vector_a, a_vec._0[3])));
   apply(uint32_to_integer_bounds(at(vector_a, b_vec._0[3])));
   apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68._0[3])));
   have 0 <= to_integer(at(vector_a, a_vec._0[3])) by { simp(); }
   have 0 <= to_integer(at(vector_a, b_vec._0[3])) by { simp(); }
   have to_integer(at(vector_a, a_vec._0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))) by { simp(); }
   have to_integer(at(vector_a, b_vec._0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))) by { simp(); }
   have 0 <= to_integer(at(vector_a, __rust_mir_68._0[3])) by { simp(); }
   have to_integer(at(vector_a, __rust_mir_68._0[3])) <= 255 by { simp(); }
   apply(adler_lane_iterator_add_contracts(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining), at(vector_a, a_vec._0[3]), at(vector_a, b_vec._0[3]), at(vector_a, __rust_mir_68._0[3]))) using { 0 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[3])); to_integer(at(vector_a, a_vec._0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[3])); to_integer(at(vector_a, b_vec._0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[3])); to_integer(at(vector_a, __rust_mir_68._0[3])) <= 255; }
   apply(adler_lane_iterator_native_preservation(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining), at(vector_a, a_vec._0[3]), at(vector_a, b_vec._0[3]), at(vector_a, __rust_mir_68._0[3]))) using { 0 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[3])); to_integer(at(vector_a, a_vec._0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[3])); to_integer(at(vector_a, b_vec._0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[3])); to_integer(at(vector_a, __rust_mir_68._0[3])) <= 255; }
   execute_until(assignment(__rust_mir_74, 0));
   have a_vec._0[0] == at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]) by { simp(); }
   have b_vec._0[0] == at(vector_a, b_vec._0[0]) by { simp(); }
   have to_integer(b_vec._0[0]) == to_integer(at(vector_a, b_vec._0[0])) by { simp() using { b_vec._0[0] == at(vector_a, b_vec._0[0]); } }
   have to_integer(a_vec._0[0]) == to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) by { simp() using { a_vec._0[0] == at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]); } }
   have to_integer(b_vec._0[0]) + to_integer(a_vec._0[0]) <= 4294967295 by { arithmetic() using { to_integer(b_vec._0[0]) == to_integer(at(vector_a, b_vec._0[0])); to_integer(a_vec._0[0]) == to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])); to_integer(at(vector_a, b_vec._0[0])) + to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) <= 4294967295; } }
   have a_vec._0[1] == at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]) by { simp(); }
   have b_vec._0[1] == at(vector_a, b_vec._0[1]) by { simp(); }
   have to_integer(b_vec._0[1]) == to_integer(at(vector_a, b_vec._0[1])) by { simp() using { b_vec._0[1] == at(vector_a, b_vec._0[1]); } }
   have to_integer(a_vec._0[1]) == to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) by { simp() using { a_vec._0[1] == at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]); } }
   have to_integer(b_vec._0[1]) + to_integer(a_vec._0[1]) <= 4294967295 by { arithmetic() using { to_integer(b_vec._0[1]) == to_integer(at(vector_a, b_vec._0[1])); to_integer(a_vec._0[1]) == to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])); to_integer(at(vector_a, b_vec._0[1])) + to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) <= 4294967295; } }
   have a_vec._0[2] == at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]) by { simp(); }
   have b_vec._0[2] == at(vector_a, b_vec._0[2]) by { simp(); }
   have to_integer(b_vec._0[2]) == to_integer(at(vector_a, b_vec._0[2])) by { simp() using { b_vec._0[2] == at(vector_a, b_vec._0[2]); } }
   have to_integer(a_vec._0[2]) == to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) by { simp() using { a_vec._0[2] == at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]); } }
   have to_integer(b_vec._0[2]) + to_integer(a_vec._0[2]) <= 4294967295 by { arithmetic() using { to_integer(b_vec._0[2]) == to_integer(at(vector_a, b_vec._0[2])); to_integer(a_vec._0[2]) == to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])); to_integer(at(vector_a, b_vec._0[2])) + to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) <= 4294967295; } }
   have a_vec._0[3] == at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]) by { simp(); }
   have b_vec._0[3] == at(vector_a, b_vec._0[3]) by { simp(); }
   have to_integer(b_vec._0[3]) == to_integer(at(vector_a, b_vec._0[3])) by { simp() using { b_vec._0[3] == at(vector_a, b_vec._0[3]); } }
   have to_integer(a_vec._0[3]) == to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) by { simp() using { a_vec._0[3] == at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]); } }
   have to_integer(b_vec._0[3]) + to_integer(a_vec._0[3]) <= 4294967295 by { arithmetic() using { to_integer(b_vec._0[3]) == to_integer(at(vector_a, b_vec._0[3])); to_integer(a_vec._0[3]) == to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])); to_integer(at(vector_a, b_vec._0[3])) + to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) <= 4294967295; } }
   mark vector_b;
   execute_until(back_edge());
   have a_vec._0[0] == at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]) by { simp(); }
   have b_vec._0[0] == at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) by { simp(); }
   have to_integer(a_vec._0[0]) == to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) by { simp() using { a_vec._0[0] == at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]); } }
   have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)) by { simp() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; } }
   have to_integer(a_vec._0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { arithmetic() using { to_integer(a_vec._0[0]) == to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); } }
   have to_integer(b_vec._0[0]) == to_integer(at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]))) by { simp() using { b_vec._0[0] == at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])); } }
   have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)) by { simp() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; } }
   have to_integer(b_vec._0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { arithmetic() using { to_integer(b_vec._0[0]) == to_integer(at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); to_integer(at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); } }
   have a_vec._0[1] == at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]) by { simp(); }
   have b_vec._0[1] == at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) by { simp(); }
   have to_integer(a_vec._0[1]) == to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) by { simp() using { a_vec._0[1] == at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]); } }
   have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)) by { simp() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; } }
   have to_integer(a_vec._0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { arithmetic() using { to_integer(a_vec._0[1]) == to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); } }
   have to_integer(b_vec._0[1]) == to_integer(at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]))) by { simp() using { b_vec._0[1] == at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])); } }
   have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)) by { simp() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; } }
   have to_integer(b_vec._0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { arithmetic() using { to_integer(b_vec._0[1]) == to_integer(at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); to_integer(at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); } }
   have a_vec._0[2] == at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]) by { simp(); }
   have b_vec._0[2] == at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) by { simp(); }
   have to_integer(a_vec._0[2]) == to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) by { simp() using { a_vec._0[2] == at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]); } }
   have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)) by { simp() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; } }
   have to_integer(a_vec._0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { arithmetic() using { to_integer(a_vec._0[2]) == to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); } }
   have to_integer(b_vec._0[2]) == to_integer(at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]))) by { simp() using { b_vec._0[2] == at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])); } }
   have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)) by { simp() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; } }
   have to_integer(b_vec._0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { arithmetic() using { to_integer(b_vec._0[2]) == to_integer(at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); to_integer(at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); } }
   have a_vec._0[3] == at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]) by { simp(); }
   have b_vec._0[3] == at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) by { simp(); }
   have to_integer(a_vec._0[3]) == to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) by { simp() using { a_vec._0[3] == at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]); } }
   have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)) by { simp() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; } }
   have to_integer(a_vec._0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { arithmetic() using { to_integer(a_vec._0[3]) == to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); } }
   have to_integer(b_vec._0[3]) == to_integer(at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]))) by { simp() using { b_vec._0[3] == at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])); } }
   have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)) by { simp() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; } }
   have to_integer(b_vec._0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) by { arithmetic() using { to_integer(b_vec._0[3]) == to_integer(at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), (int32)(uint32)__rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); to_integer(at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)(bytes_len - bytes_len % 4u64)), at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4)); } }
   have 0 <= (int32)(uint32)__rust_mir_62_remaining by { arithmetic() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); } }
   have (int32)(uint32)__rust_mir_62_remaining <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { arithmetic() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; } }
   have 0 <= (int32)(uint32)__rust_mir_62_remaining and (int32)(uint32)__rust_mir_62_remaining <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { assumption(); }
   have (int32)(uint32)__rust_mir_62_remaining % 4 == 0 by { rewrite((int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4); normalize() using { at(lane_head, (int32)(uint32)__rust_mir_62_remaining) % 4 == 0; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; } }
   have __rust_mir_62_cursor == at(lane_head, __rust_mir_62_cursor) + 4 by { simp(); }
   have __rust_mir_62_remaining <= bytes_len - bytes_len % 4u64 by { arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= bytes_len - bytes_len % 4u64; bytes_len % 4u64 <= bytes_len; } }
   have (bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining) <= 18446744073709551611u64 by { arithmetic() using { 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= bytes_len - bytes_len % 4u64; bytes_len % 4u64 <= bytes_len; } }
   have at(lane_head, __rust_mir_62_cursor) + 4 == bytes + (((bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining)) + 4u64) by { arithmetic() using { at(lane_head, __rust_mir_62_cursor) == bytes + ((bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining)); (bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining) <= 18446744073709551611u64; } }
   have (bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining == ((bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining)) + 4u64 by { arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= bytes_len - bytes_len % 4u64; bytes_len % 4u64 <= bytes_len; } }
   have __rust_mir_62_cursor == bytes + ((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining) by { rewrite((bytes_len - bytes_len % 4u64) - __rust_mir_62_remaining == ((bytes_len - bytes_len % 4u64) - at(lane_head, __rust_mir_62_remaining)) + 4u64); simp(); }
   have (at(lane_head, __rust_mir_62_remaining) - 4u64) % 4u64 == at(lane_head, __rust_mir_62_remaining % 4u64) by { normalize() using { 4u64 <= at(lane_head, __rust_mir_62_remaining); } }
   have __rust_mir_62_remaining % 4u64 == 0u64 by { rewrite(__rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64); rewrite((at(lane_head, __rust_mir_62_remaining) - 4u64) % 4u64 == at(lane_head, __rust_mir_62_remaining % 4u64)); simp(); }
   have __rust_mir_62_remaining < at(lane_head, __rust_mir_62_remaining) by { arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); } }
   have (int32)(uint32)__rust_mir_62_remaining < at(lane_head, (int32)(uint32)__rust_mir_62_remaining) by { arithmetic() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; } }
   have (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining) by { arithmetic() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)); } }
   have 0 <= (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) by { arithmetic() using { (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining); 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)); } }
   have (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) <= 2147483643 by { arithmetic() using { (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining); 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)); } }
   have truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))), 65521) == adler_spec_a(bytes, (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4), to_integer(a)) by { rewrite((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining)); simp(); }
   have 0 <= to_integer(at(vector_a, a_vec._0[0])) by { assumption(); }
   have 0 <= to_integer(at(vector_a, a_vec._0[1])) by { assumption(); }
   have 0 <= to_integer(at(vector_a, a_vec._0[2])) by { assumption(); }
   have 0 <= to_integer(at(vector_a, a_vec._0[3])) by { assumption(); }
   have 0 <= adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))) by {
    unfold(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))));
    arithmetic_certificate {
     premise 0: 0 <= to_integer(a) => 0 <= to_integer(a);
     premise 1: 0 <= to_integer(at(vector_a, a_vec._0[0])) => 0 <= to_integer(at(vector_a, a_vec._0[0]));
     premise 2: 0 <= to_integer(at(vector_a, a_vec._0[1])) => 0 <= to_integer(at(vector_a, a_vec._0[1]));
     premise 3: 0 <= to_integer(at(vector_a, a_vec._0[2])) => 0 <= to_integer(at(vector_a, a_vec._0[2]));
     premise 4: 0 <= to_integer(at(vector_a, a_vec._0[3])) => 0 <= to_integer(at(vector_a, a_vec._0[3]));
     add 0, 1 => 0 <= to_integer(a) + to_integer(at(vector_a, a_vec._0[0]));
     add 5, 2 => 0 <= to_integer(a) + to_integer(at(vector_a, a_vec._0[0])) + to_integer(at(vector_a, a_vec._0[1]));
     add 6, 3 => 0 <= to_integer(a) + to_integer(at(vector_a, a_vec._0[0])) + to_integer(at(vector_a, a_vec._0[1])) + to_integer(at(vector_a, a_vec._0[2]));
     add 7, 4 => 0 <= to_integer(a) + to_integer(at(vector_a, a_vec._0[0])) + to_integer(at(vector_a, a_vec._0[1])) + to_integer(at(vector_a, a_vec._0[2])) + to_integer(at(vector_a, a_vec._0[3]));
     conclusion 8;
    }
   }
   apply(adler_prefix_a_step_four(bytes, (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4), to_integer(a), adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))))) using { 0 <= (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4); (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) <= 2147483643; 0 <= to_integer(a); 0 <= adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))); truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))), 65521) == adler_spec_a(bytes, (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4), to_integer(a)); }
   apply(uint32_add_to_integer(at(vector_a, a_vec._0[0]), at(vector_a, __rust_mir_68._0[0]))) using { to_integer(at(vector_a, a_vec._0[0])) + to_integer(at(vector_a, __rust_mir_68._0[0])) <= 4294967295; }
   apply(uint32_add_to_integer(at(vector_a, a_vec._0[1]), at(vector_a, __rust_mir_68._0[1]))) using { to_integer(at(vector_a, a_vec._0[1])) + to_integer(at(vector_a, __rust_mir_68._0[1])) <= 4294967295; }
   apply(uint32_add_to_integer(at(vector_a, a_vec._0[2]), at(vector_a, __rust_mir_68._0[2]))) using { to_integer(at(vector_a, a_vec._0[2])) + to_integer(at(vector_a, __rust_mir_68._0[2])) <= 4294967295; }
   apply(uint32_add_to_integer(at(vector_a, a_vec._0[3]), at(vector_a, __rust_mir_68._0[3]))) using { to_integer(at(vector_a, a_vec._0[3])) + to_integer(at(vector_a, __rust_mir_68._0[3])) <= 4294967295; }
   have to_integer(at(vector_a, __rust_mir_68._0[0])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) by { normalize() using { to_integer(at(vector_a, __rust_mir_68._0[0])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 0]); } }
   have adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3])) == adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))) + (to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3])) by { unfold(adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]))); unfold(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])))); arithmetic() using { to_integer(a_vec._0[0]) == to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])); to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) == to_integer(at(vector_a, a_vec._0[0])) + to_integer(at(vector_a, __rust_mir_68._0[0])); to_integer(at(vector_a, __rust_mir_68._0[0])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]); to_integer(a_vec._0[1]) == to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])); to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) == to_integer(at(vector_a, a_vec._0[1])) + to_integer(at(vector_a, __rust_mir_68._0[1])); to_integer(at(vector_a, __rust_mir_68._0[1])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]); to_integer(a_vec._0[2]) == to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])); to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) == to_integer(at(vector_a, a_vec._0[2])) + to_integer(at(vector_a, __rust_mir_68._0[2])); to_integer(at(vector_a, __rust_mir_68._0[2])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]); to_integer(a_vec._0[3]) == to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])); to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) == to_integer(at(vector_a, a_vec._0[3])) + to_integer(at(vector_a, __rust_mir_68._0[3])); to_integer(at(vector_a, __rust_mir_68._0[3])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3]); } }
   have ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) == (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 4 by { arithmetic() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)); } }
   have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3])), 65521) == adler_spec_a(bytes, ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining), to_integer(a)) by { rewrite(adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3])) == adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))) + (to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3]))); rewrite(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) == (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 4); assumption(); }
   apply(uint32_to_integer_bounds(b)) using {};
   apply(uint32_less_equal_to_integer(a, 65520u32)) using { a <= 65520u32; }
   have to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) == to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining)) by { simp() using { (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining); } }
   have 0 <= adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))) by { rewrite(to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) == to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); simp(); }
   have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))), 65521) == adler_spec_b(bytes, (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4), to_integer(a), to_integer(b)) by { rewrite(to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) == to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining))); rewrite((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - at(lane_head, (int32)(uint32)__rust_mir_62_remaining)); simp(); }
   apply(adler_prefix_b_step_four(bytes, (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4), to_integer(a), to_integer(b), adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))), adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))))) using { 0 <= (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4); (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) <= 2147483643; 0 <= to_integer(a); to_integer(a) <= 65520; 0 <= to_integer(b); 0 <= adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))); 0 <= adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))); truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))), 65521) == adler_spec_a(bytes, (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4), to_integer(a)); truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))), 65521) == adler_spec_b(bytes, (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4), to_integer(a), to_integer(b)); }
   have (int32)(uint32)(bytes_len - bytes_len % 4u64) <= 22204 by { arithmetic() using { (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; } }
   have 4 <= ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) by { arithmetic() using { (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4; 4 <= at(lane_head, (int32)(uint32)__rust_mir_62_remaining); at(lane_head, (int32)(uint32)__rust_mir_62_remaining) <= old((int32)(uint32)(bytes_len - bytes_len % 4u64)); old((int32)(uint32)(bytes_len - bytes_len % 4u64)) <= 22204; (int32)(uint32)(bytes_len - bytes_len % 4u64) == old((int32)(uint32)(bytes_len - bytes_len % 4u64)); } }
   apply(adler_small_prefix_integer_advance((int32)(uint32)(bytes_len - bytes_len % 4u64), (int32)(uint32)__rust_mir_62_remaining)) using { 0 <= (int32)(uint32)__rust_mir_62_remaining; (int32)(uint32)__rust_mir_62_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64); (int32)(uint32)(bytes_len - bytes_len % 4u64) <= 22204; 4 <= ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining); };
   have to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a) == (to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a)) + 4 * to_integer(a) by { rewrite(to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) == to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) + 4); arithmetic_certificate special { integer_polynomial_identity bounds [] => to_integer(b) + (to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) + 4) * to_integer(a) == (to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a)) + 4 * to_integer(a); conclusion 0; } }
   apply(uint32_add_to_integer(at(vector_a, b_vec._0[0]), at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]))) using { to_integer(at(vector_a, b_vec._0[0])) + to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) <= 4294967295; }
   apply(uint32_add_to_integer(at(vector_a, b_vec._0[1]), at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]))) using { to_integer(at(vector_a, b_vec._0[1])) + to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) <= 4294967295; }
   apply(uint32_add_to_integer(at(vector_a, b_vec._0[2]), at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]))) using { to_integer(at(vector_a, b_vec._0[2])) + to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) <= 4294967295; }
   apply(uint32_add_to_integer(at(vector_a, b_vec._0[3]), at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]))) using { to_integer(at(vector_a, b_vec._0[3])) + to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) <= 4294967295; }
   have adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) == (adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))) + (4 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + 3 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]) + 2 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3]))) by { unfold(adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3]))); unfold(adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3])))); unfold(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])))); arithmetic() using { to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a) == (to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a)) + 4 * to_integer(a); to_integer(a_vec._0[0]) == to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])); to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) == to_integer(at(vector_a, a_vec._0[0])) + to_integer(at(vector_a, __rust_mir_68._0[0])); to_integer(b_vec._0[0]) == to_integer(at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]))); to_integer(at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]))) == to_integer(at(vector_a, b_vec._0[0])) + to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])); to_integer(at(vector_a, __rust_mir_68._0[0])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]); to_integer(a_vec._0[1]) == to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])); to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) == to_integer(at(vector_a, a_vec._0[1])) + to_integer(at(vector_a, __rust_mir_68._0[1])); to_integer(b_vec._0[1]) == to_integer(at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]))); to_integer(at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]))) == to_integer(at(vector_a, b_vec._0[1])) + to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])); to_integer(at(vector_a, __rust_mir_68._0[1])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]); to_integer(a_vec._0[2]) == to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])); to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) == to_integer(at(vector_a, a_vec._0[2])) + to_integer(at(vector_a, __rust_mir_68._0[2])); to_integer(b_vec._0[2]) == to_integer(at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]))); to_integer(at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]))) == to_integer(at(vector_a, b_vec._0[2])) + to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])); to_integer(at(vector_a, __rust_mir_68._0[2])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]); to_integer(a_vec._0[3]) == to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])); to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) == to_integer(at(vector_a, a_vec._0[3])) + to_integer(at(vector_a, __rust_mir_68._0[3])); to_integer(b_vec._0[3]) == to_integer(at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]))); to_integer(at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]))) == to_integer(at(vector_a, b_vec._0[3])) + to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])); to_integer(at(vector_a, __rust_mir_68._0[3])) == to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3]); } }
   have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])), 65521) == adler_spec_b(bytes, ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining), to_integer(a), to_integer(b)) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) == (adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))) + (4 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + 3 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]) + 2 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3])))); rewrite(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) == (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 4); assumption(); }
   apply(adler_byte_bounds(bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)])) using { 0 <= (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4); (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) <= 2147483643; };
   apply(adler_byte_bounds(bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1])) using { 0 <= (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4); (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) <= 2147483643; };
   apply(adler_byte_bounds(bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2])) using { 0 <= (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4); (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) <= 2147483643; };
   apply(adler_byte_bounds(bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3])) using { 0 <= (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4); (((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) <= 2147483643; };
   have 0 <= adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))) by { arithmetic() using { 0 <= adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))); 0 <= adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))); } }
   have 0 <= (4 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)])) by { arithmetic() using { 0 <= to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]); } }
   have 0 <= (4 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + 3 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1])) by { arithmetic() using { 0 <= to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]); 0 <= to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]); } }
   have 0 <= (4 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + 3 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]) + 2 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2])) by { arithmetic() using { 0 <= (4 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + 3 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1])); 0 <= to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]); } }
   have 0 <= (4 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + 3 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]) + 2 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3])) by { arithmetic() using { 0 <= (4 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + 3 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]) + 2 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2])); 0 <= to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3]); } }
   have 0 <= adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) == (adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))) + (4 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + 3 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]) + 2 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3])))); arithmetic() using { 0 <= adler_lane_b(to_integer(b) + to_integer((((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3])), to_integer(at(vector_a, b_vec._0[0])), to_integer(at(vector_a, b_vec._0[1])), to_integer(at(vector_a, b_vec._0[2])), to_integer(at(vector_a, b_vec._0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec._0[0])), to_integer(at(vector_a, a_vec._0[1])), to_integer(at(vector_a, a_vec._0[2])), to_integer(at(vector_a, a_vec._0[3]))); 0 <= (4 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4)]) + 3 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 1]) + 2 * to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 2]) + to_integer((int32)bytes[(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) - 4) + 3])); } }
   apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)(bytes_len - bytes_len % 4u64), (int32)(uint32)__rust_mir_62_remaining)) using { 0 <= (int32)(uint32)__rust_mir_62_remaining; (int32)(uint32)__rust_mir_62_remaining <= (int32)(uint32)(bytes_len - bytes_len % 4u64); }
   close_invariants by { assumption(); }
  }
 }
 have __rust_mir_62_remaining < 4u64 by { cases { not (0u64 < __rust_mir_62_remaining) => { arithmetic() using { not 0u64 < __rust_mir_62_remaining; } } not (4u64 <= __rust_mir_62_remaining) => { assumption(); } } }
 have __rust_mir_62_remaining % 4u64 == __rust_mir_62_remaining by { normalize() using { __rust_mir_62_remaining < 4u64; } }
 have __rust_mir_62_remaining == 0u64 by { simp(); }
 have (int32)(uint32)__rust_mir_62_remaining == 0 by { rewrite(__rust_mir_62_remaining == 0u64); normalize(); }
 have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3])), 65521) == adler_spec_a(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(a)) by {
  have (int32)(uint32)(bytes_len - bytes_len % 4u64) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining by { rewrite((int32)(uint32)__rust_mir_62_remaining == 0); normalize(); }
  rewrite((int32)(uint32)(bytes_len - bytes_len % 4u64) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining);
  assumption();
 }
 have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])), 65521) == adler_spec_b(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(a), to_integer(b)) by {
  have (int32)(uint32)(bytes_len - bytes_len % 4u64) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining by { rewrite((int32)(uint32)__rust_mir_62_remaining == 0); normalize(); }
  have to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) == to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) by { simp() using { (int32)(uint32)(bytes_len - bytes_len % 4u64) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining; } }
  have adler_lane_b(to_integer(b) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) == adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) by { rewrite(to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) == to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining))); simp(); }
  have adler_spec_b(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(a), to_integer(b)) == adler_spec_b(bytes, ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining), to_integer(a), to_integer(b)) by { simp() using { (int32)(uint32)(bytes_len - bytes_len % 4u64) == (int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining; } }
  rewrite(adler_lane_b(to_integer(b) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) == adler_lane_b(to_integer(b) + to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])));
  rewrite(adler_spec_b(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(a), to_integer(b)) == adler_spec_b(bytes, ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining), to_integer(a), to_integer(b)));
  assumption();
 }
 have 0 <= adler_lane_b(to_integer(b) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(a), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])) by {
  have (int32)(uint32)(bytes_len - bytes_len % 4u64) == ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining) by { rewrite((int32)(uint32)__rust_mir_62_remaining == 0); normalize(); }
  have to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) == to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining)) by { simp() using { (int32)(uint32)(bytes_len - bytes_len % 4u64) == ((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining); } }
  rewrite(to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) == to_integer(((int32)(uint32)(bytes_len - bytes_len % 4u64) - (int32)(uint32)__rust_mir_62_remaining))); assumption();
 }
 mark vector_prefix;
 have truncating_remainder(adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec._0[1])), to_integer(at(vector_prefix, a_vec._0[2])), to_integer(at(vector_prefix, a_vec._0[3])), to_integer(at(vector_prefix, b_vec._0[0])), to_integer(at(vector_prefix, b_vec._0[1])), to_integer(at(vector_prefix, b_vec._0[2])), to_integer(at(vector_prefix, b_vec._0[3]))), 65521) == adler_spec_b(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b))) by { simp(); }
 have 0 <= adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec._0[1])), to_integer(at(vector_prefix, a_vec._0[2])), to_integer(at(vector_prefix, a_vec._0[3])), to_integer(at(vector_prefix, b_vec._0[0])), to_integer(at(vector_prefix, b_vec._0[1])), to_integer(at(vector_prefix, b_vec._0[2])), to_integer(at(vector_prefix, b_vec._0[3]))) by { simp(); }
 have truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec._0[0])), to_integer(at(vector_prefix, a_vec._0[1])), to_integer(at(vector_prefix, a_vec._0[2])), to_integer(at(vector_prefix, a_vec._0[3]))), 65521) == adler_spec_a(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(at(vector_prefix, a))) by { simp(); }
 apply(uint32_to_integer_bounds(at(vector_prefix, a))) using {};
 apply(uint32_to_integer_bounds(at(vector_prefix, a_vec._0[0]))) using {};
 apply(uint32_to_integer_bounds(at(vector_prefix, a_vec._0[1]))) using {};
 apply(uint32_to_integer_bounds(at(vector_prefix, a_vec._0[2]))) using {};
 apply(uint32_to_integer_bounds(at(vector_prefix, a_vec._0[3]))) using {};
 apply(adler_lane_a_reduction(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec._0[0])), to_integer(at(vector_prefix, a_vec._0[1])), to_integer(at(vector_prefix, a_vec._0[2])), to_integer(at(vector_prefix, a_vec._0[3])))) using { 0 <= to_integer(at(vector_prefix, a)); 0 <= to_integer(at(vector_prefix, a_vec._0[0])); 0 <= to_integer(at(vector_prefix, a_vec._0[1])); 0 <= to_integer(at(vector_prefix, a_vec._0[2])); 0 <= to_integer(at(vector_prefix, a_vec._0[3])); };
 have remainder_len == bytes_len - (bytes_len - bytes_len % 4u64) by { simp() using {}; }
 have remainder_len == bytes_len % 4u64 by { rewrite(remainder_len == bytes_len - (bytes_len - bytes_len % 4u64)); apply(adler_small_tail_metadata(bytes_len)) using { bytes_len <= 22207u64; } assumption(); }
 execute_until(assignment(__rust_mir_80, 0)); step();
 have __rust_mir_77 == (uint32)remainder_chunk_len by { simp(); }
 have remainder_chunk_len == bytes_len - bytes_len % 4u64 by { assumption(); }
 apply(adler_small_length_cast(bytes_len - bytes_len % 4u64)) using { bytes_len - bytes_len % 4u64 <= 22204u64; }
 have __rust_mir_77 <= 22204u32 by { rewrite(__rust_mir_77 == (uint32)remainder_chunk_len); rewrite(remainder_chunk_len == bytes_len - bytes_len % 4u64); assumption(); }
 have __rust_mir_80 <= 65520u32 by { simp() using { a <= 65520u32; } }
 apply(adler_scalar_batch_product_bound(__rust_mir_77, __rust_mir_80)) using { __rust_mir_77 <= 22204u32; __rust_mir_80 <= 65520u32; }
 have to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 4294967295 by { arithmetic() using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 1454806080; } }
 apply(uint32_mul_guard_by_integer_bound(__rust_mir_77, __rust_mir_80)) using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 4294967295; }
 have bytes_len - bytes_len % 4u64 <= 22208u64 by { arithmetic() using { bytes_len - bytes_len % 4u64 <= 22204u64; } }
 apply(adler_count_observation(bytes_len - bytes_len % 4u64)) using { bytes_len - bytes_len % 4u64 <= 22208u64; };
 have __rust_mir_77 == (uint32)(bytes_len - bytes_len % 4u64) by { simp() using { __rust_mir_77 == (uint32)remainder_chunk_len; remainder_chunk_len == bytes_len - bytes_len % 4u64; } }
 have to_integer(__rust_mir_77) == to_integer((uint32)(bytes_len - bytes_len % 4u64)) by { simp() using { __rust_mir_77 == (uint32)(bytes_len - bytes_len % 4u64); } }
 have to_integer(__rust_mir_77) == to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { arithmetic() using { to_integer(__rust_mir_77) == to_integer((uint32)(bytes_len - bytes_len % 4u64)); to_integer((uint32)(bytes_len - bytes_len % 4u64)) == to_integer(bytes_len - bytes_len % 4u64); to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) == to_integer(bytes_len - bytes_len % 4u64); } }
 mark seed_product;
 have to_integer(at(seed_product, __rust_mir_77)) == to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) by { simp(); }
 have to_integer(at(seed_product, __rust_mir_80)) == to_integer(at(vector_prefix, a)) by { simp(); }
 have to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80)) <= 1454806080 by { simp() using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 1454806080; } }
 have at(seed_product, __rust_mir_80) == 0u32 or at(seed_product, __rust_mir_77) <= 4294967295u32 / at(seed_product, __rust_mir_80) by { simp() using { __rust_mir_80 == 0u32 or __rust_mir_77 <= 4294967295u32 / __rust_mir_80; } }
 apply(uint32_mul_to_integer(at(seed_product, __rust_mir_77), at(seed_product, __rust_mir_80))) using { at(seed_product, __rust_mir_80) == 0u32 or at(seed_product, __rust_mir_77) <= 4294967295u32 / at(seed_product, __rust_mir_80); }
 if __rust_mir_80 == 0u32 {
  execute_until(assignment(__rust_mir_76, 0)); step();
 } else {
  have __rust_mir_77 <= 4294967295u32 / __rust_mir_80 by {
   cases {
    __rust_mir_80 == 0u32 => { contradiction(not (__rust_mir_80 == 0u32)); }
    __rust_mir_77 <= 4294967295u32 / __rust_mir_80 => { assumption(); }
   }
  }
  execute_until(assignment(__rust_mir_76, 0)); step();
 }
 have __rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80) by { simp(); }
 have to_integer(__rust_mir_76) == to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)) by { rewrite(__rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)); rewrite(to_integer(at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)) == to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80))); rewrite(to_integer(at(seed_product, __rust_mir_77)) == to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64))); rewrite(to_integer(at(seed_product, __rust_mir_80)) == to_integer(at(vector_prefix, a))); simp(); }
 have to_integer(__rust_mir_76) <= 1454806080 by { rewrite(__rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)); rewrite(to_integer(at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)) == to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80))); assumption(); }
 have b <= 65520u32 by { assumption(); }
 apply(uint32_less_equal_to_integer(b, 65520u32)) using { b <= 65520u32; }
 have to_integer(b) + to_integer(__rust_mir_76) <= 4294967295 by { arithmetic() using { to_integer(b) <= 65520; to_integer(__rust_mir_76) <= 1454806080; } }
 apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_76)) using { to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; }
 mark deferred_b;
 have to_integer(at(deferred_b, b)) == to_integer(at(vector_prefix, b)) by { simp(); }
 have to_integer(at(deferred_b, __rust_mir_76)) == to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)) by { simp(); }
 have to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)) <= 4294967295 by { simp() using { to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; } }
 apply(uint32_add_to_integer(at(deferred_b, b), at(deferred_b, __rust_mir_76))) using { to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)) <= 4294967295; };
 execute_until(assignment(__rust_mir_84, 0)); step();
 mark reduction_a;
 have to_integer(at(reduction_a, a_vec._0[0])) == to_integer(at(vector_prefix, a_vec._0[0])) by { simp(); }
 have to_integer(at(reduction_a, a_vec._0[1])) == to_integer(at(vector_prefix, a_vec._0[1])) by { simp(); }
 have to_integer(at(reduction_a, a_vec._0[2])) == to_integer(at(vector_prefix, a_vec._0[2])) by { simp(); }
 have to_integer(at(reduction_a, a_vec._0[3])) == to_integer(at(vector_prefix, a_vec._0[3])) by { simp(); }
 execute_until(assignment(__rust_mir_86, 0)); step();
 mark reduction_b;
 have to_integer(at(reduction_b, b_vec._0[0])) == to_integer(at(vector_prefix, b_vec._0[0])) by { simp(); }
 have to_integer(at(reduction_b, b_vec._0[1])) == to_integer(at(vector_prefix, b_vec._0[1])) by { simp(); }
 have to_integer(at(reduction_b, b_vec._0[2])) == to_integer(at(vector_prefix, b_vec._0[2])) by { simp(); }
 have to_integer(at(reduction_b, b_vec._0[3])) == to_integer(at(vector_prefix, b_vec._0[3])) by { simp(); }
 execute_until(assignment(__rust_mir_88, 0));
 have __rust_checked_77 == at(deferred_b, b) + at(deferred_b, __rust_mir_76) by { simp(); }
 have to_integer(__rust_checked_77) == to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)) by { simp() using { __rust_checked_77 == at(deferred_b, b) + at(deferred_b, __rust_mir_76); } }
 have to_integer(__rust_checked_77) == to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)) by { arithmetic() using { to_integer(__rust_checked_77) == to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)); to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)) == to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)); to_integer(at(deferred_b, b)) == to_integer(at(vector_prefix, b)); to_integer(at(deferred_b, __rust_mir_76)) == to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)); } }

 apply(uint32_to_integer_bounds(__rust_checked_77)) using {};
 have 0 <= to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)) by { arithmetic() using { 0 <= to_integer(__rust_checked_77); to_integer(__rust_checked_77) == to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)); } }
 apply(uint32_to_integer_bounds(at(vector_prefix, b_vec._0[0]))) using {};
 apply(uint32_to_integer_bounds(at(vector_prefix, b_vec._0[1]))) using {};
 apply(uint32_to_integer_bounds(at(vector_prefix, b_vec._0[2]))) using {};
 apply(uint32_to_integer_bounds(at(vector_prefix, b_vec._0[3]))) using {};
 apply(adler_lane_b_reduction(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec._0[1])), to_integer(at(vector_prefix, a_vec._0[2])), to_integer(at(vector_prefix, a_vec._0[3])), to_integer(at(vector_prefix, b_vec._0[0])), to_integer(at(vector_prefix, b_vec._0[1])), to_integer(at(vector_prefix, b_vec._0[2])), to_integer(at(vector_prefix, b_vec._0[3])))) using { 0 <= to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)); 0 <= to_integer(at(vector_prefix, a_vec._0[1])); 0 <= to_integer(at(vector_prefix, a_vec._0[2])); 0 <= to_integer(at(vector_prefix, a_vec._0[3])); 0 <= to_integer(at(vector_prefix, b_vec._0[0])); 0 <= to_integer(at(vector_prefix, b_vec._0[1])); 0 <= to_integer(at(vector_prefix, b_vec._0[2])); 0 <= to_integer(at(vector_prefix, b_vec._0[3])); 0 <= adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec._0[1])), to_integer(at(vector_prefix, a_vec._0[2])), to_integer(at(vector_prefix, a_vec._0[3])), to_integer(at(vector_prefix, b_vec._0[0])), to_integer(at(vector_prefix, b_vec._0[1])), to_integer(at(vector_prefix, b_vec._0[2])), to_integer(at(vector_prefix, b_vec._0[3]))); };
 have __rust_checked_82 == 65521u32 by { simp(); }
 have 65521u32 == __rust_checked_82 by { simp() using { __rust_checked_82 == 65521u32; } }
 have b_vec._0[0] < __rust_checked_82 by { simp(); }
 have b_vec._0[0] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
 have b_vec._0[0] <= 4294967295u32 / 4u32 by { arithmetic() using { b_vec._0[0] < 65521u32; } }
 have b_vec._0[1] < __rust_checked_82 by { simp(); }
 have b_vec._0[1] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
 have b_vec._0[1] <= 4294967295u32 / 4u32 by { arithmetic() using { b_vec._0[1] < 65521u32; } }
 have b_vec._0[2] < __rust_checked_82 by { simp(); }
 have b_vec._0[2] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
 have b_vec._0[2] <= 4294967295u32 / 4u32 by { arithmetic() using { b_vec._0[2] < 65521u32; } }
 have b_vec._0[3] < __rust_checked_82 by { simp(); }
 have b_vec._0[3] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
 have b_vec._0[3] <= 4294967295u32 / 4u32 by { arithmetic() using { b_vec._0[3] < 65521u32; } }
 apply(uint32_less_than_to_integer(b_vec._0[0], 65521u32)) using { b_vec._0[0] < 65521u32; }
 have to_integer(b_vec._0[0]) <= 65520 by { arithmetic() using { to_integer(b_vec._0[0]) < 65521; } }
 apply(uint32_less_than_to_integer(b_vec._0[1], 65521u32)) using { b_vec._0[1] < 65521u32; }
 have to_integer(b_vec._0[1]) <= 65520 by { arithmetic() using { to_integer(b_vec._0[1]) < 65521; } }
 apply(uint32_less_than_to_integer(b_vec._0[2], 65521u32)) using { b_vec._0[2] < 65521u32; }
 have to_integer(b_vec._0[2]) <= 65520 by { arithmetic() using { to_integer(b_vec._0[2]) < 65521; } }
 apply(uint32_less_than_to_integer(b_vec._0[3], 65521u32)) using { b_vec._0[3] < 65521u32; }
 have to_integer(b_vec._0[3]) <= 65520 by { arithmetic() using { to_integer(b_vec._0[3]) < 65521; } }
 have to_integer(a) == to_integer(at(vector_prefix, a)) by { simp(); }
 have __rust_checked_84 == 65521u32 by { simp(); }
 have a_vec._0[0] == at(reduction_a, a_vec._0[0]) % __rust_checked_84 by { simp(); }
 have a_vec._0[0] == at(reduction_a, a_vec._0[0]) % 65521u32 by { rewrite(a_vec._0[0] == at(reduction_a, a_vec._0[0]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
 apply(uint32_remainder_to_integer(at(reduction_a, a_vec._0[0]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
 have to_integer(a_vec._0[0]) == to_integer(at(reduction_a, a_vec._0[0]) % 65521u32) by { simp() using { a_vec._0[0] == at(reduction_a, a_vec._0[0]) % 65521u32; } }
 have truncating_remainder(to_integer(at(reduction_a, a_vec._0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[0])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec._0[0])) == to_integer(at(vector_prefix, a_vec._0[0]))); simp(); }
 have to_integer(a_vec._0[0]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[0])), 65521) by { arithmetic() using { to_integer(a_vec._0[0]) == to_integer(at(reduction_a, a_vec._0[0]) % 65521u32); to_integer(at(reduction_a, a_vec._0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec._0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec._0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[0])), 65521); } }
 have a_vec._0[1] == at(reduction_a, a_vec._0[1]) % __rust_checked_84 by { simp(); }
 have a_vec._0[1] == at(reduction_a, a_vec._0[1]) % 65521u32 by { rewrite(a_vec._0[1] == at(reduction_a, a_vec._0[1]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
 apply(uint32_remainder_to_integer(at(reduction_a, a_vec._0[1]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
 have to_integer(a_vec._0[1]) == to_integer(at(reduction_a, a_vec._0[1]) % 65521u32) by { simp() using { a_vec._0[1] == at(reduction_a, a_vec._0[1]) % 65521u32; } }
 have truncating_remainder(to_integer(at(reduction_a, a_vec._0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[1])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec._0[1])) == to_integer(at(vector_prefix, a_vec._0[1]))); simp(); }
 have to_integer(a_vec._0[1]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[1])), 65521) by { arithmetic() using { to_integer(a_vec._0[1]) == to_integer(at(reduction_a, a_vec._0[1]) % 65521u32); to_integer(at(reduction_a, a_vec._0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec._0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec._0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[1])), 65521); } }
 have a_vec._0[2] == at(reduction_a, a_vec._0[2]) % __rust_checked_84 by { simp(); }
 have a_vec._0[2] == at(reduction_a, a_vec._0[2]) % 65521u32 by { rewrite(a_vec._0[2] == at(reduction_a, a_vec._0[2]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
 apply(uint32_remainder_to_integer(at(reduction_a, a_vec._0[2]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
 have to_integer(a_vec._0[2]) == to_integer(at(reduction_a, a_vec._0[2]) % 65521u32) by { simp() using { a_vec._0[2] == at(reduction_a, a_vec._0[2]) % 65521u32; } }
 have truncating_remainder(to_integer(at(reduction_a, a_vec._0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[2])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec._0[2])) == to_integer(at(vector_prefix, a_vec._0[2]))); simp(); }
 have to_integer(a_vec._0[2]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[2])), 65521) by { arithmetic() using { to_integer(a_vec._0[2]) == to_integer(at(reduction_a, a_vec._0[2]) % 65521u32); to_integer(at(reduction_a, a_vec._0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec._0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec._0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[2])), 65521); } }
 have a_vec._0[3] == at(reduction_a, a_vec._0[3]) % __rust_checked_84 by { simp(); }
 have a_vec._0[3] == at(reduction_a, a_vec._0[3]) % 65521u32 by { rewrite(a_vec._0[3] == at(reduction_a, a_vec._0[3]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
 apply(uint32_remainder_to_integer(at(reduction_a, a_vec._0[3]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
 have to_integer(a_vec._0[3]) == to_integer(at(reduction_a, a_vec._0[3]) % 65521u32) by { simp() using { a_vec._0[3] == at(reduction_a, a_vec._0[3]) % 65521u32; } }
 have truncating_remainder(to_integer(at(reduction_a, a_vec._0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[3])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec._0[3])) == to_integer(at(vector_prefix, a_vec._0[3]))); simp(); }
 have to_integer(a_vec._0[3]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[3])), 65521) by { arithmetic() using { to_integer(a_vec._0[3]) == to_integer(at(reduction_a, a_vec._0[3]) % 65521u32); to_integer(at(reduction_a, a_vec._0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec._0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec._0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[3])), 65521); } }
 have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3])), 65521) == adler_spec_a(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(at(vector_prefix, a))) by { rewrite(to_integer(a) == to_integer(at(vector_prefix, a))); rewrite(to_integer(a_vec._0[0]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[0])), 65521)); rewrite(to_integer(a_vec._0[1]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[1])), 65521)); rewrite(to_integer(a_vec._0[2]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[2])), 65521)); rewrite(to_integer(a_vec._0[3]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[3])), 65521)); arithmetic() using { truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec._0[0])), to_integer(at(vector_prefix, a_vec._0[1])), to_integer(at(vector_prefix, a_vec._0[2])), to_integer(at(vector_prefix, a_vec._0[3]))), 65521) == truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), truncating_remainder(to_integer(at(vector_prefix, a_vec._0[0])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec._0[1])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec._0[2])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec._0[3])), 65521)), 65521); truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec._0[0])), to_integer(at(vector_prefix, a_vec._0[1])), to_integer(at(vector_prefix, a_vec._0[2])), to_integer(at(vector_prefix, a_vec._0[3]))), 65521) == adler_spec_a(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(at(vector_prefix, a))); } }
 have b_vec._0[0] == at(reduction_b, b_vec._0[0]) % __rust_checked_82 by { simp(); }
 have b_vec._0[0] == at(reduction_b, b_vec._0[0]) % 65521u32 by { rewrite(b_vec._0[0] == at(reduction_b, b_vec._0[0]) % __rust_checked_82); simp() using { __rust_checked_82 == 65521u32; } }
 apply(uint32_remainder_to_integer(at(reduction_b, b_vec._0[0]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
 have to_integer(b_vec._0[0]) == to_integer(at(reduction_b, b_vec._0[0]) % 65521u32) by { simp() using { b_vec._0[0] == at(reduction_b, b_vec._0[0]) % 65521u32; } }
 have truncating_remainder(to_integer(at(reduction_b, b_vec._0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[0])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec._0[0])) == to_integer(at(vector_prefix, b_vec._0[0]))); simp(); }
 have to_integer(b_vec._0[0]) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[0])), 65521) by { arithmetic() using { to_integer(b_vec._0[0]) == to_integer(at(reduction_b, b_vec._0[0]) % 65521u32); to_integer(at(reduction_b, b_vec._0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec._0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec._0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[0])), 65521); } }
 have b_vec._0[1] == at(reduction_b, b_vec._0[1]) % __rust_checked_82 by { simp(); }
 have b_vec._0[1] == at(reduction_b, b_vec._0[1]) % 65521u32 by { rewrite(b_vec._0[1] == at(reduction_b, b_vec._0[1]) % __rust_checked_82); simp() using { __rust_checked_82 == 65521u32; } }
 apply(uint32_remainder_to_integer(at(reduction_b, b_vec._0[1]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
 have to_integer(b_vec._0[1]) == to_integer(at(reduction_b, b_vec._0[1]) % 65521u32) by { simp() using { b_vec._0[1] == at(reduction_b, b_vec._0[1]) % 65521u32; } }
 have truncating_remainder(to_integer(at(reduction_b, b_vec._0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[1])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec._0[1])) == to_integer(at(vector_prefix, b_vec._0[1]))); simp(); }
 have to_integer(b_vec._0[1]) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[1])), 65521) by { arithmetic() using { to_integer(b_vec._0[1]) == to_integer(at(reduction_b, b_vec._0[1]) % 65521u32); to_integer(at(reduction_b, b_vec._0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec._0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec._0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[1])), 65521); } }
 have b_vec._0[2] == at(reduction_b, b_vec._0[2]) % __rust_checked_82 by { simp(); }
 have b_vec._0[2] == at(reduction_b, b_vec._0[2]) % 65521u32 by { rewrite(b_vec._0[2] == at(reduction_b, b_vec._0[2]) % __rust_checked_82); simp() using { __rust_checked_82 == 65521u32; } }
 apply(uint32_remainder_to_integer(at(reduction_b, b_vec._0[2]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
 have to_integer(b_vec._0[2]) == to_integer(at(reduction_b, b_vec._0[2]) % 65521u32) by { simp() using { b_vec._0[2] == at(reduction_b, b_vec._0[2]) % 65521u32; } }
 have truncating_remainder(to_integer(at(reduction_b, b_vec._0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[2])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec._0[2])) == to_integer(at(vector_prefix, b_vec._0[2]))); simp(); }
 have to_integer(b_vec._0[2]) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[2])), 65521) by { arithmetic() using { to_integer(b_vec._0[2]) == to_integer(at(reduction_b, b_vec._0[2]) % 65521u32); to_integer(at(reduction_b, b_vec._0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec._0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec._0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[2])), 65521); } }
 have b_vec._0[3] == at(reduction_b, b_vec._0[3]) % __rust_checked_82 by { simp(); }
 have b_vec._0[3] == at(reduction_b, b_vec._0[3]) % 65521u32 by { rewrite(b_vec._0[3] == at(reduction_b, b_vec._0[3]) % __rust_checked_82); simp() using { __rust_checked_82 == 65521u32; } }
 apply(uint32_remainder_to_integer(at(reduction_b, b_vec._0[3]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
 have to_integer(b_vec._0[3]) == to_integer(at(reduction_b, b_vec._0[3]) % 65521u32) by { simp() using { b_vec._0[3] == at(reduction_b, b_vec._0[3]) % 65521u32; } }
 have truncating_remainder(to_integer(at(reduction_b, b_vec._0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[3])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec._0[3])) == to_integer(at(vector_prefix, b_vec._0[3]))); simp(); }
 have to_integer(b_vec._0[3]) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[3])), 65521) by { arithmetic() using { to_integer(b_vec._0[3]) == to_integer(at(reduction_b, b_vec._0[3]) % 65521u32); to_integer(at(reduction_b, b_vec._0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec._0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec._0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[3])), 65521); } }
 have __rust_checked_79 == 65521u32 by { simp(); }
 have b == __rust_checked_77 % __rust_checked_79 by { simp(); }
 have b == __rust_checked_77 % 65521u32 by { rewrite(b == __rust_checked_77 % __rust_checked_79); simp() using { __rust_checked_79 == 65521u32; } }
 apply(uint32_remainder_to_integer(__rust_checked_77, 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
 have to_integer(b) == to_integer(__rust_checked_77 % 65521u32) by { simp() using { b == __rust_checked_77 % 65521u32; } }
 have truncating_remainder(to_integer(__rust_checked_77), 65521) == truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), 65521) by { rewrite(to_integer(__rust_checked_77) == to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a))); simp(); }
 have to_integer(b) == truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), 65521) by { arithmetic() using { to_integer(b) == to_integer(__rust_checked_77 % 65521u32); to_integer(__rust_checked_77 % 65521u32) == truncating_remainder(to_integer(__rust_checked_77), to_integer(65521u32)); truncating_remainder(to_integer(__rust_checked_77), 65521) == truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), 65521); } }
 have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]), to_integer(b_vec._0[0]), to_integer(b_vec._0[1]), to_integer(b_vec._0[2]), to_integer(b_vec._0[3])), 65521) == adler_spec_b(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b))) by { rewrite(to_integer(b) == truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), 65521)); rewrite(to_integer(a_vec._0[1]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[1])), 65521)); rewrite(to_integer(a_vec._0[2]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[2])), 65521)); rewrite(to_integer(a_vec._0[3]) == truncating_remainder(to_integer(at(vector_prefix, a_vec._0[3])), 65521)); rewrite(to_integer(b_vec._0[0]) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[0])), 65521)); rewrite(to_integer(b_vec._0[1]) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[1])), 65521)); rewrite(to_integer(b_vec._0[2]) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[2])), 65521)); rewrite(to_integer(b_vec._0[3]) == truncating_remainder(to_integer(at(vector_prefix, b_vec._0[3])), 65521)); arithmetic() using { truncating_remainder(adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec._0[1])), to_integer(at(vector_prefix, a_vec._0[2])), to_integer(at(vector_prefix, a_vec._0[3])), to_integer(at(vector_prefix, b_vec._0[0])), to_integer(at(vector_prefix, b_vec._0[1])), to_integer(at(vector_prefix, b_vec._0[2])), to_integer(at(vector_prefix, b_vec._0[3]))), 65521) == truncating_remainder(adler_lane_b(truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec._0[1])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec._0[2])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec._0[3])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec._0[0])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec._0[1])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec._0[2])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec._0[3])), 65521)), 65521); truncating_remainder(adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((int32)(uint32)(bytes_len - bytes_len % 4u64)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec._0[1])), to_integer(at(vector_prefix, a_vec._0[2])), to_integer(at(vector_prefix, a_vec._0[3])), to_integer(at(vector_prefix, b_vec._0[0])), to_integer(at(vector_prefix, b_vec._0[1])), to_integer(at(vector_prefix, b_vec._0[2])), to_integer(at(vector_prefix, b_vec._0[3]))), 65521) == adler_spec_b(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b))); } }
 mark weighted_b;
 have truncating_remainder(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec._0[1])), to_integer(at(weighted_b, a_vec._0[2])), to_integer(at(weighted_b, a_vec._0[3])), to_integer(at(weighted_b, b_vec._0[0])), to_integer(at(weighted_b, b_vec._0[1])), to_integer(at(weighted_b, b_vec._0[2])), to_integer(at(weighted_b, b_vec._0[3]))), 65521) == adler_spec_b(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b))) by { simp(); }
 execute_until(assignment(__rust_mir_91, 0));
 have __rust_checked_85 == 65521u32 by { simp(); }
 have 65521u32 == __rust_checked_85 by { simp() using { __rust_checked_85 == 65521u32; } }
 have a_vec._0[0] < __rust_checked_85 by { simp(); }
 have a_vec._0[0] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
 have a_vec._0[1] < __rust_checked_85 by { simp(); }
 have a_vec._0[1] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
 have a_vec._0[2] < __rust_checked_85 by { simp(); }
 have a_vec._0[2] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
 have a_vec._0[3] < __rust_checked_85 by { simp(); }
 have a_vec._0[3] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
 have to_integer(b_vec._0[0]) == to_integer(at(weighted_b, b_vec._0[0])) * 4 by { simp(); }
 have to_integer(at(weighted_b, b_vec._0[0])) <= 65520 by { simp(); }
 have to_integer(b_vec._0[0]) <= 262080 by { arithmetic() using { to_integer(b_vec._0[0]) == to_integer(at(weighted_b, b_vec._0[0])) * 4; to_integer(at(weighted_b, b_vec._0[0])) <= 65520; } }
 have to_integer(b_vec._0[1]) == to_integer(at(weighted_b, b_vec._0[1])) * 4 by { simp(); }
 have to_integer(at(weighted_b, b_vec._0[1])) <= 65520 by { simp(); }
 have to_integer(b_vec._0[1]) <= 262080 by { arithmetic() using { to_integer(b_vec._0[1]) == to_integer(at(weighted_b, b_vec._0[1])) * 4; to_integer(at(weighted_b, b_vec._0[1])) <= 65520; } }
 have to_integer(b_vec._0[2]) == to_integer(at(weighted_b, b_vec._0[2])) * 4 by { simp(); }
 have to_integer(at(weighted_b, b_vec._0[2])) <= 65520 by { simp(); }
 have to_integer(b_vec._0[2]) <= 262080 by { arithmetic() using { to_integer(b_vec._0[2]) == to_integer(at(weighted_b, b_vec._0[2])) * 4; to_integer(at(weighted_b, b_vec._0[2])) <= 65520; } }
 have to_integer(b_vec._0[3]) == to_integer(at(weighted_b, b_vec._0[3])) * 4 by { simp(); }
 have to_integer(at(weighted_b, b_vec._0[3])) <= 65520 by { simp(); }
 have to_integer(b_vec._0[3]) <= 262080 by { arithmetic() using { to_integer(b_vec._0[3]) == to_integer(at(weighted_b, b_vec._0[3])) * 4; to_integer(at(weighted_b, b_vec._0[3])) <= 65520; } }
 mark correction_b;
 have to_integer(at(correction_b, b_vec._0[1])) == to_integer(at(weighted_b, b_vec._0[1])) * 4 by { simp(); }
 have to_integer(at(correction_b, a_vec._0[1])) == to_integer(at(weighted_b, a_vec._0[1])) by { simp(); }
 have to_integer(at(correction_b, b_vec._0[2])) == to_integer(at(weighted_b, b_vec._0[2])) * 4 by { simp(); }
 have to_integer(at(correction_b, a_vec._0[2])) == to_integer(at(weighted_b, a_vec._0[2])) by { simp(); }
 have to_integer(at(correction_b, b_vec._0[3])) == to_integer(at(weighted_b, b_vec._0[3])) * 4 by { simp(); }
 have to_integer(at(correction_b, a_vec._0[3])) == to_integer(at(weighted_b, a_vec._0[3])) by { simp(); }
 apply(adler_recombine_lane_1(a_vec._0[1], b_vec._0[1])) using { a_vec._0[1] < 65521u32; to_integer(b_vec._0[1]) <= 262080; }
 apply(adler_recombine_lane_2(a_vec._0[2], b_vec._0[2])) using { a_vec._0[2] < 65521u32; to_integer(b_vec._0[2]) <= 262080; }
 apply(adler_recombine_lane_3(a_vec._0[3], b_vec._0[3])) using { a_vec._0[3] < 65521u32; to_integer(b_vec._0[3]) <= 262080; }
 apply(adler_recombine_difference(a_vec._0[2])) using { a_vec._0[2] < 65521u32; }
 have 65521u32 - a_vec._0[2] <= 4294967295u32 / 2u32 by { arithmetic() using { 65521u32 - a_vec._0[2] <= 65521u32; } }
 apply(adler_recombine_difference(a_vec._0[3])) using { a_vec._0[3] < 65521u32; }
 have 65521u32 - a_vec._0[3] <= 4294967295u32 / 3u32 by { arithmetic() using { 65521u32 - a_vec._0[3] <= 65521u32; } }
 have to_integer(at(correction_b, b_vec._0[1]) + (65521u32 - at(correction_b, a_vec._0[1]))) == to_integer(at(correction_b, b_vec._0[1])) + (65521 - to_integer(at(correction_b, a_vec._0[1]))) * 1 by { simp(); }
 have to_integer(at(correction_b, b_vec._0[2]) + ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32)) == to_integer(at(correction_b, b_vec._0[2])) + (65521 - to_integer(at(correction_b, a_vec._0[2]))) * 2 by { simp(); }
 have to_integer(at(correction_b, b_vec._0[3]) + ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32)) == to_integer(at(correction_b, b_vec._0[3])) + (65521 - to_integer(at(correction_b, a_vec._0[3]))) * 3 by { simp(); }
 execute_until(assignment(__rust_mir_94, 0));
 have __rust_mir_89 == (65521u32 - at(correction_b, a_vec._0[1])) by { simp(); }
 have b_vec._0[1] == at(correction_b, b_vec._0[1]) by { simp(); }
 mark correction_add_1;
 have at(correction_add_1, __rust_mir_89) == (65521u32 - at(correction_b, a_vec._0[1])) by { simp(); }
 have at(correction_add_1, b_vec._0[1]) == at(correction_b, b_vec._0[1]) by { simp(); }
 step();
 have __rust_mir_94 == at(correction_add_1, b_vec._0[1]) + at(correction_add_1, __rust_mir_89) by { simp(); }
 have __rust_mir_94 == at(correction_b, b_vec._0[1]) + (65521u32 - at(correction_b, a_vec._0[1])) by { rewrite(__rust_mir_94 == at(correction_add_1, b_vec._0[1]) + at(correction_add_1, __rust_mir_89)); rewrite(at(correction_add_1, b_vec._0[1]) == at(correction_b, b_vec._0[1])); rewrite(at(correction_add_1, __rust_mir_89) == (65521u32 - at(correction_b, a_vec._0[1]))); simp(); }
 mark correction_store_1;
 have at(correction_store_1, __rust_mir_94) == at(correction_b, b_vec._0[1]) + (65521u32 - at(correction_b, a_vec._0[1])) by { simp(); }
 execute_until(assignment(__rust_mir_102, 0));
 have __rust_mir_95 == ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32) by { simp(); }
 have b_vec._0[2] == at(correction_b, b_vec._0[2]) by { simp(); }
 mark correction_add_2;
 have at(correction_add_2, __rust_mir_95) == ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32) by { simp(); }
 have at(correction_add_2, b_vec._0[2]) == at(correction_b, b_vec._0[2]) by { simp(); }
 step();
 have __rust_mir_102 == at(correction_add_2, b_vec._0[2]) + at(correction_add_2, __rust_mir_95) by { simp(); }
 have __rust_mir_102 == at(correction_b, b_vec._0[2]) + ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32) by { rewrite(__rust_mir_102 == at(correction_add_2, b_vec._0[2]) + at(correction_add_2, __rust_mir_95)); rewrite(at(correction_add_2, b_vec._0[2]) == at(correction_b, b_vec._0[2])); rewrite(at(correction_add_2, __rust_mir_95) == ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32)); simp(); }
 mark correction_store_2;
 have at(correction_store_2, __rust_mir_102) == at(correction_b, b_vec._0[2]) + ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32) by { simp(); }
 execute_until(assignment(__rust_mir_104, 0)); step();
 have __rust_mir_104 == 65521u32 - at(correction_b, a_vec._0[3]) by { simp(); }
 execute_until(assignment(__rust_mir_108, 0));
 mark correction_multiply_3;
 have at(correction_multiply_3, __rust_mir_104) == 65521u32 - at(correction_b, a_vec._0[3]) by { simp(); }
 step();
 have __rust_mir_108 == at(correction_multiply_3, __rust_mir_104) * 3u32 by { simp(); }
 have __rust_mir_108 == (65521u32 - at(correction_b, a_vec._0[3])) * 3u32 by { rewrite(__rust_mir_108 == at(correction_multiply_3, __rust_mir_104) * 3u32); rewrite(at(correction_multiply_3, __rust_mir_104) == 65521u32 - at(correction_b, a_vec._0[3])); simp(); }
 execute_until(assignment(__rust_mir_103, 0)); step();
 have __rust_mir_103 == (65521u32 - at(correction_b, a_vec._0[3])) * 3u32 by { simp() using { __rust_mir_108 == (65521u32 - at(correction_b, a_vec._0[3])) * 3u32; } }
 execute_until(assignment(__rust_mir_110, 0));
 have b_vec._0[3] == at(correction_b, b_vec._0[3]) by { simp(); }
 mark correction_add_3;
 have at(correction_add_3, __rust_mir_103) == ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32) by { simp(); }
 have at(correction_add_3, b_vec._0[3]) == at(correction_b, b_vec._0[3]) by { simp(); }
 step();
 have __rust_mir_110 == at(correction_add_3, b_vec._0[3]) + at(correction_add_3, __rust_mir_103) by { simp(); }
 have __rust_mir_110 == at(correction_b, b_vec._0[3]) + ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32) by { rewrite(__rust_mir_110 == at(correction_add_3, b_vec._0[3]) + at(correction_add_3, __rust_mir_103)); rewrite(at(correction_add_3, b_vec._0[3]) == at(correction_b, b_vec._0[3])); rewrite(at(correction_add_3, __rust_mir_103) == ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32)); simp(); }
 mark correction_store_3;
 have at(correction_store_3, __rust_mir_110) == at(correction_b, b_vec._0[3]) + ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32) by { simp(); }
 execute_until(loop(3));
 have b_vec._0[1] == at(correction_store_1, __rust_mir_94) by { simp(); }
 have b_vec._0[1] == at(correction_b, b_vec._0[1]) + (65521u32 - at(correction_b, a_vec._0[1])) by { rewrite(b_vec._0[1] == at(correction_store_1, __rust_mir_94)); rewrite(at(correction_store_1, __rust_mir_94) == at(correction_b, b_vec._0[1]) + (65521u32 - at(correction_b, a_vec._0[1]))); simp(); }
 have to_integer(b_vec._0[1]) == to_integer(at(correction_b, b_vec._0[1]) + (65521u32 - at(correction_b, a_vec._0[1]))) by { simp() using { b_vec._0[1] == at(correction_b, b_vec._0[1]) + (65521u32 - at(correction_b, a_vec._0[1])); } }
 have to_integer(b_vec._0[1]) == to_integer(at(weighted_b, b_vec._0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec._0[1]))) * 1 by { arithmetic() using { to_integer(b_vec._0[1]) == to_integer(at(correction_b, b_vec._0[1]) + (65521u32 - at(correction_b, a_vec._0[1]))); to_integer(at(correction_b, b_vec._0[1]) + (65521u32 - at(correction_b, a_vec._0[1]))) == to_integer(at(correction_b, b_vec._0[1])) + (65521 - to_integer(at(correction_b, a_vec._0[1]))) * 1; to_integer(at(correction_b, b_vec._0[1])) == to_integer(at(weighted_b, b_vec._0[1])) * 4; to_integer(at(correction_b, a_vec._0[1])) == to_integer(at(weighted_b, a_vec._0[1])); } }
 have b_vec._0[2] == at(correction_store_2, __rust_mir_102) by { simp(); }
 have b_vec._0[2] == at(correction_b, b_vec._0[2]) + ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32) by { rewrite(b_vec._0[2] == at(correction_store_2, __rust_mir_102)); rewrite(at(correction_store_2, __rust_mir_102) == at(correction_b, b_vec._0[2]) + ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32)); simp(); }
 have to_integer(b_vec._0[2]) == to_integer(at(correction_b, b_vec._0[2]) + ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32)) by { simp() using { b_vec._0[2] == at(correction_b, b_vec._0[2]) + ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32); } }
 have to_integer(b_vec._0[2]) == to_integer(at(weighted_b, b_vec._0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec._0[2]))) * 2 by { arithmetic() using { to_integer(b_vec._0[2]) == to_integer(at(correction_b, b_vec._0[2]) + ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32)); to_integer(at(correction_b, b_vec._0[2]) + ((65521u32 - at(correction_b, a_vec._0[2])) * 2u32)) == to_integer(at(correction_b, b_vec._0[2])) + (65521 - to_integer(at(correction_b, a_vec._0[2]))) * 2; to_integer(at(correction_b, b_vec._0[2])) == to_integer(at(weighted_b, b_vec._0[2])) * 4; to_integer(at(correction_b, a_vec._0[2])) == to_integer(at(weighted_b, a_vec._0[2])); } }
 have b_vec._0[3] == at(correction_store_3, __rust_mir_110) by { simp(); }
 have b_vec._0[3] == at(correction_b, b_vec._0[3]) + ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32) by { rewrite(b_vec._0[3] == at(correction_store_3, __rust_mir_110)); rewrite(at(correction_store_3, __rust_mir_110) == at(correction_b, b_vec._0[3]) + ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32)); simp(); }
 have to_integer(b_vec._0[3]) == to_integer(at(correction_b, b_vec._0[3]) + ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32)) by { simp() using { b_vec._0[3] == at(correction_b, b_vec._0[3]) + ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32); } }
 have to_integer(b_vec._0[3]) == to_integer(at(weighted_b, b_vec._0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec._0[3]))) * 3 by { arithmetic() using { to_integer(b_vec._0[3]) == to_integer(at(correction_b, b_vec._0[3]) + ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32)); to_integer(at(correction_b, b_vec._0[3]) + ((65521u32 - at(correction_b, a_vec._0[3])) * 3u32)) == to_integer(at(correction_b, b_vec._0[3])) + (65521 - to_integer(at(correction_b, a_vec._0[3]))) * 3; to_integer(at(correction_b, b_vec._0[3])) == to_integer(at(weighted_b, b_vec._0[3])) * 4; to_integer(at(correction_b, a_vec._0[3])) == to_integer(at(weighted_b, a_vec._0[3])); } }
 have to_integer(b_vec._0[0]) == to_integer(at(weighted_b, b_vec._0[0])) * 4 by { simp(); }
 have a <= 65520u32 by { assumption(); }
 apply(uint32_less_equal_to_integer(a, 65520u32)) using { a <= 65520u32; }
 execute_until(assignment(__rust_mir_121, 0));
 have av == a_vec._0[0] by { simp(); }
 apply(uint32_less_than_to_integer(a_vec._0[0], 65521u32)) using { a_vec._0[0] < 65521u32; }
 have to_integer(av) <= 65520 by { rewrite(av == a_vec._0[0]); arithmetic() using { to_integer(a_vec._0[0]) < 65521; } }
 step();
 have to_integer(__rust_mir_121) <= 65520 by { simp() using { to_integer(av) <= 65520; } }
 have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by { arithmetic() using { to_integer(a) <= 65520; to_integer(__rust_mir_121) <= 65520; } }
 apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
 execute_until(assignment(__rust_mir_122, 0));
 mark small_sum_a_0;
 have to_integer(at(small_sum_a_0, a)) == to_integer(at(vector_prefix, a)) by { simp(); }
 have to_integer(at(small_sum_a_0, __rust_mir_121)) == to_integer(a_vec._0[0]) by { simp(); }
 have to_integer(at(small_sum_a_0, a)) <= 65520 by { simp() using { to_integer(a) <= 65520; } }
 have to_integer(at(small_sum_a_0, __rust_mir_121)) <= 65520 by { simp() using { to_integer(__rust_mir_121) <= 65520; } }
 have to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_a_0, a)) <= 65520; to_integer(at(small_sum_a_0, __rust_mir_121)) <= 65520; } }
 step();
 have __rust_mir_122 == at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_a_0, a), at(small_sum_a_0, __rust_mir_121))) using { to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)) <= 4294967295; }
 have to_integer(__rust_mir_122) <= 131040 by { rewrite(__rust_mir_122 == at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121)); rewrite(to_integer(at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121)) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121))); arithmetic() using { to_integer(at(small_sum_a_0, a)) <= 65520; to_integer(at(small_sum_a_0, __rust_mir_121)) <= 65520; } }
 execute_until(assignment(a, 1)); step();
 have to_integer(a) <= 131040 by { simp() using { to_integer(__rust_mir_122) <= 131040; } }
 have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)) by { simp() using { __rust_mir_122 == at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121); to_integer(at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121)) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)); } }
 have to_integer(a) == to_integer(__rust_mir_122) by { simp(); }
 have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec._0[0]) by { arithmetic() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)); to_integer(at(small_sum_a_0, a)) == to_integer(at(vector_prefix, a)); to_integer(at(small_sum_a_0, __rust_mir_121)) == to_integer(a_vec._0[0]); } }

 step(); step(); step(); step(); step(); step(); step(); step();
 execute_until(assignment(__rust_mir_121, 0));
 have av == a_vec._0[1] by { simp(); }
 apply(uint32_less_than_to_integer(a_vec._0[1], 65521u32)) using { a_vec._0[1] < 65521u32; }
 have to_integer(av) <= 65520 by { rewrite(av == a_vec._0[1]); arithmetic() using { to_integer(a_vec._0[1]) < 65521; } }
 step();
 have to_integer(__rust_mir_121) <= 65520 by { simp() using { to_integer(av) <= 65520; } }
 have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by { arithmetic() using { to_integer(a) <= 131040; to_integer(__rust_mir_121) <= 65520; } }
 apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
 execute_until(assignment(__rust_mir_122, 0));
 mark small_sum_a_1;
 have to_integer(at(small_sum_a_1, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec._0[0]) by { simp(); }
 have to_integer(at(small_sum_a_1, __rust_mir_121)) == to_integer(a_vec._0[1]) by { simp(); }
 have to_integer(at(small_sum_a_1, a)) <= 131040 by { simp() using { to_integer(a) <= 131040; } }
 have to_integer(at(small_sum_a_1, __rust_mir_121)) <= 65520 by { simp() using { to_integer(__rust_mir_121) <= 65520; } }
 have to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_a_1, a)) <= 131040; to_integer(at(small_sum_a_1, __rust_mir_121)) <= 65520; } }
 step();
 have __rust_mir_122 == at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_a_1, a), at(small_sum_a_1, __rust_mir_121))) using { to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)) <= 4294967295; }
 have to_integer(__rust_mir_122) <= 196560 by { rewrite(__rust_mir_122 == at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121)); rewrite(to_integer(at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121)) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121))); arithmetic() using { to_integer(at(small_sum_a_1, a)) <= 131040; to_integer(at(small_sum_a_1, __rust_mir_121)) <= 65520; } }
 execute_until(assignment(a, 1)); step();
 have to_integer(a) <= 196560 by { simp() using { to_integer(__rust_mir_122) <= 196560; } }
 have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)) by { simp() using { __rust_mir_122 == at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121); to_integer(at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121)) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)); } }
 have to_integer(a) == to_integer(__rust_mir_122) by { simp(); }
 have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec._0[0]) + to_integer(a_vec._0[1]) by { arithmetic() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)); to_integer(at(small_sum_a_1, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec._0[0]); to_integer(at(small_sum_a_1, __rust_mir_121)) == to_integer(a_vec._0[1]); } }

 step(); step(); step(); step(); step(); step(); step(); step();
 execute_until(assignment(__rust_mir_121, 0));
 have av == a_vec._0[2] by { simp(); }
 apply(uint32_less_than_to_integer(a_vec._0[2], 65521u32)) using { a_vec._0[2] < 65521u32; }
 have to_integer(av) <= 65520 by { rewrite(av == a_vec._0[2]); arithmetic() using { to_integer(a_vec._0[2]) < 65521; } }
 step();
 have to_integer(__rust_mir_121) <= 65520 by { simp() using { to_integer(av) <= 65520; } }
 have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by { arithmetic() using { to_integer(a) <= 196560; to_integer(__rust_mir_121) <= 65520; } }
 apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
 execute_until(assignment(__rust_mir_122, 0));
 mark small_sum_a_2;
 have to_integer(at(small_sum_a_2, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec._0[0]) + to_integer(a_vec._0[1]) by { simp(); }
 have to_integer(at(small_sum_a_2, __rust_mir_121)) == to_integer(a_vec._0[2]) by { simp(); }
 have to_integer(at(small_sum_a_2, a)) <= 196560 by { simp() using { to_integer(a) <= 196560; } }
 have to_integer(at(small_sum_a_2, __rust_mir_121)) <= 65520 by { simp() using { to_integer(__rust_mir_121) <= 65520; } }
 have to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_a_2, a)) <= 196560; to_integer(at(small_sum_a_2, __rust_mir_121)) <= 65520; } }
 step();
 have __rust_mir_122 == at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_a_2, a), at(small_sum_a_2, __rust_mir_121))) using { to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)) <= 4294967295; }
 have to_integer(__rust_mir_122) <= 262080 by { rewrite(__rust_mir_122 == at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121)); rewrite(to_integer(at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121)) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121))); arithmetic() using { to_integer(at(small_sum_a_2, a)) <= 196560; to_integer(at(small_sum_a_2, __rust_mir_121)) <= 65520; } }
 execute_until(assignment(a, 1)); step();
 have to_integer(a) <= 262080 by { simp() using { to_integer(__rust_mir_122) <= 262080; } }
 have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)) by { simp() using { __rust_mir_122 == at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121); to_integer(at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121)) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)); } }
 have to_integer(a) == to_integer(__rust_mir_122) by { simp(); }
 have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec._0[0]) + to_integer(a_vec._0[1]) + to_integer(a_vec._0[2]) by { arithmetic() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)); to_integer(at(small_sum_a_2, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec._0[0]) + to_integer(a_vec._0[1]); to_integer(at(small_sum_a_2, __rust_mir_121)) == to_integer(a_vec._0[2]); } }

 step(); step(); step(); step(); step(); step(); step(); step();
 execute_until(assignment(__rust_mir_121, 0));
 have av == a_vec._0[3] by { simp(); }
 apply(uint32_less_than_to_integer(a_vec._0[3], 65521u32)) using { a_vec._0[3] < 65521u32; }
 have to_integer(av) <= 65520 by { rewrite(av == a_vec._0[3]); arithmetic() using { to_integer(a_vec._0[3]) < 65521; } }
 step();
 have to_integer(__rust_mir_121) <= 65520 by { simp() using { to_integer(av) <= 65520; } }
 have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by { arithmetic() using { to_integer(a) <= 262080; to_integer(__rust_mir_121) <= 65520; } }
 apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
 execute_until(assignment(__rust_mir_122, 0));
 mark small_sum_a_3;
 have to_integer(at(small_sum_a_3, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec._0[0]) + to_integer(a_vec._0[1]) + to_integer(a_vec._0[2]) by { simp(); }
 have to_integer(at(small_sum_a_3, __rust_mir_121)) == to_integer(a_vec._0[3]) by { simp(); }
 have to_integer(at(small_sum_a_3, a)) <= 262080 by { simp() using { to_integer(a) <= 262080; } }
 have to_integer(at(small_sum_a_3, __rust_mir_121)) <= 65520 by { simp() using { to_integer(__rust_mir_121) <= 65520; } }
 have to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_a_3, a)) <= 262080; to_integer(at(small_sum_a_3, __rust_mir_121)) <= 65520; } }
 step();
 have __rust_mir_122 == at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_a_3, a), at(small_sum_a_3, __rust_mir_121))) using { to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)) <= 4294967295; }
 have to_integer(__rust_mir_122) <= 327600 by { rewrite(__rust_mir_122 == at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121)); rewrite(to_integer(at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121)) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121))); arithmetic() using { to_integer(at(small_sum_a_3, a)) <= 262080; to_integer(at(small_sum_a_3, __rust_mir_121)) <= 65520; } }
 execute_until(assignment(a, 1)); step();
 have to_integer(a) <= 327600 by { simp() using { to_integer(__rust_mir_122) <= 327600; } }
 have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)) by { simp() using { __rust_mir_122 == at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121); to_integer(at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121)) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)); } }
 have to_integer(a) == to_integer(__rust_mir_122) by { simp(); }
 have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec._0[0]) + to_integer(a_vec._0[1]) + to_integer(a_vec._0[2]) + to_integer(a_vec._0[3]) by { arithmetic() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)); to_integer(at(small_sum_a_3, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec._0[0]) + to_integer(a_vec._0[1]) + to_integer(a_vec._0[2]); to_integer(at(small_sum_a_3, __rust_mir_121)) == to_integer(a_vec._0[3]); } }

 step(); step(); step(); step(); step(); step(); step(); step();
 have to_integer(a) == adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3])) by { unfold(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]))); assumption(); }
 have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(at(vector_prefix, a))) by { rewrite(to_integer(a) == adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(a_vec._0[0]), to_integer(a_vec._0[1]), to_integer(a_vec._0[2]), to_integer(a_vec._0[3]))); assumption(); }
 execute_until(loop(4));
 have __rust_checked_79 == 65521u32 by { simp(); }
 have 65521u32 == __rust_checked_79 by { simp() using { __rust_checked_79 == 65521u32; } }
 have b == __rust_checked_77 % __rust_checked_79 by { simp(); }
 have __rust_checked_79 != 0u32 by { rewrite(__rust_checked_79 == 65521u32); normalize(); }
 apply(uint32_remainder_less_than_divisor(__rust_checked_77, __rust_checked_79)) using { __rust_checked_79 != 0u32; }
 have b < __rust_checked_79 by { rewrite(b == __rust_checked_77 % __rust_checked_79); assumption(); }
 have b < 65521u32 by { rewrite(65521u32 == __rust_checked_79); assumption(); }
 apply(uint32_less_than_to_integer(b, 65521u32)) using { b < 65521u32; }
 have to_integer(b) <= 65520 by { arithmetic() using { to_integer(b) < 65521; } }
 have to_integer(b_vec._0[0]) <= 262080 by { simp(); }
 execute_until(assignment(__rust_mir_133, 0));
 have bv == b_vec._0[0] by { simp(); }
 have to_integer(bv) <= 262080 by { rewrite(bv == b_vec._0[0]); assumption(); }
 step();
 have to_integer(__rust_mir_133) <= 262080 by { simp() using { to_integer(bv) <= 262080; } }
 have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by { arithmetic() using { to_integer(b) <= 65520; to_integer(__rust_mir_133) <= 262080; } }
 apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
 execute_until(assignment(__rust_mir_134, 0));
 mark small_sum_b_0;
 have to_integer(at(small_sum_b_0, b)) == to_integer(at(weighted_b, b)) by { simp(); }
 have to_integer(at(small_sum_b_0, __rust_mir_133)) == to_integer(b_vec._0[0]) by { simp(); }
 have to_integer(at(small_sum_b_0, b)) <= 65520 by { simp() using { to_integer(b) <= 65520; } }
 have to_integer(at(small_sum_b_0, __rust_mir_133)) <= 262080 by { simp() using { to_integer(__rust_mir_133) <= 262080; } }
 have to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_b_0, b)) <= 65520; to_integer(at(small_sum_b_0, __rust_mir_133)) <= 262080; } }
 step();
 have __rust_mir_134 == at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_b_0, b), at(small_sum_b_0, __rust_mir_133))) using { to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)) <= 4294967295; }
 have to_integer(__rust_mir_134) <= 327600 by { rewrite(__rust_mir_134 == at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133)); rewrite(to_integer(at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133)) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133))); arithmetic() using { to_integer(at(small_sum_b_0, b)) <= 65520; to_integer(at(small_sum_b_0, __rust_mir_133)) <= 262080; } }
 execute_until(assignment(b, 5)); step();
 have to_integer(b) <= 327600 by { simp() using { to_integer(__rust_mir_134) <= 327600; } }
 have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)) by { simp() using { __rust_mir_134 == at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133); to_integer(at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133)) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)); } }
 have to_integer(b) == to_integer(__rust_mir_134) by { simp(); }
 have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]) by { arithmetic() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)); to_integer(at(small_sum_b_0, b)) == to_integer(at(weighted_b, b)); to_integer(at(small_sum_b_0, __rust_mir_133)) == to_integer(b_vec._0[0]); } }

 step(); step(); step(); step(); step(); step(); step(); step();
 have to_integer(b_vec._0[1]) <= 327601 by { simp(); }
 execute_until(assignment(__rust_mir_133, 0));
 have bv == b_vec._0[1] by { simp(); }
 have to_integer(bv) <= 327601 by { rewrite(bv == b_vec._0[1]); assumption(); }
 step();
 have to_integer(__rust_mir_133) <= 327601 by { simp() using { to_integer(bv) <= 327601; } }
 have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by { arithmetic() using { to_integer(b) <= 327600; to_integer(__rust_mir_133) <= 327601; } }
 apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
 execute_until(assignment(__rust_mir_134, 0));
 mark small_sum_b_1;
 have to_integer(at(small_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]) by { simp(); }
 have to_integer(at(small_sum_b_1, __rust_mir_133)) == to_integer(b_vec._0[1]) by { simp(); }
 have to_integer(at(small_sum_b_1, b)) <= 327600 by { simp() using { to_integer(b) <= 327600; } }
 have to_integer(at(small_sum_b_1, __rust_mir_133)) <= 327601 by { simp() using { to_integer(__rust_mir_133) <= 327601; } }
 have to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_b_1, b)) <= 327600; to_integer(at(small_sum_b_1, __rust_mir_133)) <= 327601; } }
 step();
 have __rust_mir_134 == at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_b_1, b), at(small_sum_b_1, __rust_mir_133))) using { to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)) <= 4294967295; }
 have to_integer(__rust_mir_134) <= 655201 by { rewrite(__rust_mir_134 == at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133)); rewrite(to_integer(at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133)) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133))); arithmetic() using { to_integer(at(small_sum_b_1, b)) <= 327600; to_integer(at(small_sum_b_1, __rust_mir_133)) <= 327601; } }
 execute_until(assignment(b, 5)); step();
 have to_integer(b) <= 655201 by { simp() using { to_integer(__rust_mir_134) <= 655201; } }
 have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)) by { simp() using { __rust_mir_134 == at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133); to_integer(at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133)) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)); } }
 have to_integer(b) == to_integer(__rust_mir_134) by { simp(); }
 have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]) + to_integer(b_vec._0[1]) by { arithmetic() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)); to_integer(at(small_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]); to_integer(at(small_sum_b_1, __rust_mir_133)) == to_integer(b_vec._0[1]); } }

 step(); step(); step(); step(); step(); step(); step(); step();
 have to_integer(b_vec._0[2]) <= 393122 by { simp(); }
 execute_until(assignment(__rust_mir_133, 0));
 have bv == b_vec._0[2] by { simp(); }
 have to_integer(bv) <= 393122 by { rewrite(bv == b_vec._0[2]); assumption(); }
 step();
 have to_integer(__rust_mir_133) <= 393122 by { simp() using { to_integer(bv) <= 393122; } }
 have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by { arithmetic() using { to_integer(b) <= 655201; to_integer(__rust_mir_133) <= 393122; } }
 apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
 execute_until(assignment(__rust_mir_134, 0));
 mark small_sum_b_2;
 have to_integer(at(small_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]) + to_integer(b_vec._0[1]) by { simp(); }
 have to_integer(at(small_sum_b_2, __rust_mir_133)) == to_integer(b_vec._0[2]) by { simp(); }
 have to_integer(at(small_sum_b_2, b)) <= 655201 by { simp() using { to_integer(b) <= 655201; } }
 have to_integer(at(small_sum_b_2, __rust_mir_133)) <= 393122 by { simp() using { to_integer(__rust_mir_133) <= 393122; } }
 have to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_b_2, b)) <= 655201; to_integer(at(small_sum_b_2, __rust_mir_133)) <= 393122; } }
 step();
 have __rust_mir_134 == at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_b_2, b), at(small_sum_b_2, __rust_mir_133))) using { to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)) <= 4294967295; }
 have to_integer(__rust_mir_134) <= 1048323 by { rewrite(__rust_mir_134 == at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133)); rewrite(to_integer(at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133)) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133))); arithmetic() using { to_integer(at(small_sum_b_2, b)) <= 655201; to_integer(at(small_sum_b_2, __rust_mir_133)) <= 393122; } }
 execute_until(assignment(b, 5)); step();
 have to_integer(b) <= 1048323 by { simp() using { to_integer(__rust_mir_134) <= 1048323; } }
 have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)) by { simp() using { __rust_mir_134 == at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133); to_integer(at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133)) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)); } }
 have to_integer(b) == to_integer(__rust_mir_134) by { simp(); }
 have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]) + to_integer(b_vec._0[1]) + to_integer(b_vec._0[2]) by { arithmetic() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)); to_integer(at(small_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]) + to_integer(b_vec._0[1]); to_integer(at(small_sum_b_2, __rust_mir_133)) == to_integer(b_vec._0[2]); } }

 step(); step(); step(); step(); step(); step(); step(); step();
 have to_integer(b_vec._0[3]) <= 458643 by { simp(); }
 execute_until(assignment(__rust_mir_133, 0));
 have bv == b_vec._0[3] by { simp(); }
 have to_integer(bv) <= 458643 by { rewrite(bv == b_vec._0[3]); assumption(); }
 step();
 have to_integer(__rust_mir_133) <= 458643 by { simp() using { to_integer(bv) <= 458643; } }
 have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by { arithmetic() using { to_integer(b) <= 1048323; to_integer(__rust_mir_133) <= 458643; } }
 apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
 execute_until(assignment(__rust_mir_134, 0));
 mark small_sum_b_3;
 have to_integer(at(small_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]) + to_integer(b_vec._0[1]) + to_integer(b_vec._0[2]) by { simp(); }
 have to_integer(at(small_sum_b_3, __rust_mir_133)) == to_integer(b_vec._0[3]) by { simp(); }
 have to_integer(at(small_sum_b_3, b)) <= 1048323 by { simp() using { to_integer(b) <= 1048323; } }
 have to_integer(at(small_sum_b_3, __rust_mir_133)) <= 458643 by { simp() using { to_integer(__rust_mir_133) <= 458643; } }
 have to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_b_3, b)) <= 1048323; to_integer(at(small_sum_b_3, __rust_mir_133)) <= 458643; } }
 step();
 have __rust_mir_134 == at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_b_3, b), at(small_sum_b_3, __rust_mir_133))) using { to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)) <= 4294967295; }
 have to_integer(__rust_mir_134) <= 1506966 by { rewrite(__rust_mir_134 == at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133)); rewrite(to_integer(at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133)) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133))); arithmetic() using { to_integer(at(small_sum_b_3, b)) <= 1048323; to_integer(at(small_sum_b_3, __rust_mir_133)) <= 458643; } }
 execute_until(assignment(b, 5)); step();
 have to_integer(b) <= 1506966 by { simp() using { to_integer(__rust_mir_134) <= 1506966; } }
 have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)) by { simp() using { __rust_mir_134 == at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133); to_integer(at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133)) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)); } }
 have to_integer(b) == to_integer(__rust_mir_134) by { simp(); }
 have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]) + to_integer(b_vec._0[1]) + to_integer(b_vec._0[2]) + to_integer(b_vec._0[3]) by { arithmetic() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)); to_integer(at(small_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]) + to_integer(b_vec._0[1]) + to_integer(b_vec._0[2]); to_integer(at(small_sum_b_3, __rust_mir_133)) == to_integer(b_vec._0[3]); } }

 step(); step(); step(); step(); step(); step(); step(); step();
 have remainder_len == bytes_len % 4u64 by { assumption(); }
 apply(adler_small_tail_metadata(bytes_len)) using { bytes_len <= 22207u64; }
 have remainder_len <= 3u64 by { rewrite(remainder_len == bytes_len % 4u64); assumption(); }
 have remainder_len <= 2147483647u64 by { normalize() using { remainder_len <= 3u64; } }
 have to_integer(b) == adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec._0[1])), to_integer(at(weighted_b, a_vec._0[2])), to_integer(at(weighted_b, a_vec._0[3])), to_integer(at(weighted_b, b_vec._0[0])), to_integer(at(weighted_b, b_vec._0[1])), to_integer(at(weighted_b, b_vec._0[2])), to_integer(at(weighted_b, b_vec._0[3]))) by { unfold(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec._0[1])), to_integer(at(weighted_b, a_vec._0[2])), to_integer(at(weighted_b, a_vec._0[3])), to_integer(at(weighted_b, b_vec._0[0])), to_integer(at(weighted_b, b_vec._0[1])), to_integer(at(weighted_b, b_vec._0[2])), to_integer(at(weighted_b, b_vec._0[3])))); arithmetic() using { to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec._0[0]) + to_integer(b_vec._0[1]) + to_integer(b_vec._0[2]) + to_integer(b_vec._0[3]); to_integer(b_vec._0[0]) == to_integer(at(weighted_b, b_vec._0[0])) * 4; to_integer(b_vec._0[1]) == to_integer(at(weighted_b, b_vec._0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec._0[1]))) * 1; to_integer(b_vec._0[2]) == to_integer(at(weighted_b, b_vec._0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec._0[2]))) * 2; to_integer(b_vec._0[3]) == to_integer(at(weighted_b, b_vec._0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec._0[3]))) * 3; } }
 have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, (int32)(uint32)(bytes_len - bytes_len % 4u64), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b))) by { rewrite(to_integer(b) == adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec._0[1])), to_integer(at(weighted_b, a_vec._0[2])), to_integer(at(weighted_b, a_vec._0[3])), to_integer(at(weighted_b, b_vec._0[0])), to_integer(at(weighted_b, b_vec._0[1])), to_integer(at(weighted_b, b_vec._0[2])), to_integer(at(weighted_b, b_vec._0[3])))); assumption(); }
 execute_until(loop(5));
 apply(adler_small_prefix_within_full(bytes_len)) using { bytes_len <= 22207u64; }
 apply(adler_small_signed_tail(bytes_len)) using { bytes_len <= 22207u64; }
 apply(adler_small_tail_indices(bytes_len)) using { bytes_len <= 22207u64; }
 have (int32)(uint32)remainder_len == (int32)(uint32)(bytes_len % 4u64) by { rewrite(remainder_len == bytes_len % 4u64); normalize() using {}; }
 have 0 <= (int32)(uint32)remainder_len by { rewrite((int32)(uint32)remainder_len == (int32)(uint32)(bytes_len % 4u64)); assumption(); }
 have (int32)(uint32)remainder_len <= 3 by { rewrite((int32)(uint32)remainder_len == (int32)(uint32)(bytes_len % 4u64)); assumption(); }
 have (int32)(uint32)remainder_len <= (int32)(uint32)bytes_len by { rewrite((int32)(uint32)remainder_len == (int32)(uint32)(bytes_len % 4u64)); assumption(); }
 have (int32)(uint32)bytes_len - (int32)(uint32)remainder_len == (int32)(uint32)(bytes_len - bytes_len % 4u64) by { rewrite((int32)(uint32)remainder_len == (int32)(uint32)(bytes_len % 4u64)); assumption(); }
  have __rust_mir_138_remaining == remainder_len by { simp(); }
  have (int32)(uint32)__rust_mir_138_remaining == (int32)(uint32)remainder_len by { rewrite(__rust_mir_138_remaining == remainder_len); normalize(); }
  have remainder_len <= 3u64 by { rewrite(remainder_len == bytes_len % 4u64); assumption(); }
  have remainder_len <= bytes_len by { rewrite(remainder_len == bytes_len % 4u64); normalize(); }
  have __rust_mir_138_remaining <= remainder_len by { rewrite(__rust_mir_138_remaining == remainder_len); normalize(); }
 have 0 <= (int32)(uint32)__rust_mir_138_remaining and (int32)(uint32)__rust_mir_138_remaining <= (int32)(uint32)remainder_len by { rewrite((int32)(uint32)__rust_mir_138_remaining == (int32)(uint32)remainder_len); both { assumption(); } and { normalize() using {}; } }
  have __rust_mir_138_cursor == remainder by { normalize(); }
  have remainder == bytes + (bytes_len - bytes_len % 4u64) by { normalize(); }
  have bytes_len - __rust_mir_138_remaining == bytes_len - bytes_len % 4u64 by { rewrite(__rust_mir_138_remaining == remainder_len); rewrite(remainder_len == bytes_len % 4u64); normalize(); }
  have __rust_mir_138_cursor == bytes + (bytes_len - __rust_mir_138_remaining) by { rewrite(bytes_len - __rust_mir_138_remaining == bytes_len - bytes_len % 4u64); rewrite(__rust_mir_138_cursor == remainder); assumption(); }
 have adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining) == 0 by { unfold(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining)); rewrite((int32)(uint32)__rust_mir_138_remaining == (int32)(uint32)remainder_len); arithmetic() using {}; }
 have adler_tail_a_ceiling(0) == 327600 by { unfold(adler_tail_a_ceiling(0)); normalize() using {}; }
 have adler_tail_b_ceiling(0) == 1506966 by { unfold(adler_tail_b_ceiling(0)); normalize() using {}; }
 apply(uint32_to_integer_bounds(a));
 apply(uint32_to_integer_bounds(b));
 have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining)) by { rewrite(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining) == 0); rewrite(adler_tail_a_ceiling(0) == 327600); assumption(); }
 have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining)) by { rewrite(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining) == 0); rewrite(adler_tail_b_ceiling(0) == 1506966); assumption(); }
 have old(to_integer((uint32)self->a)) == to_integer(at(vector_prefix, a)) by { simp(); }
 have old(to_integer((uint32)self->b)) == to_integer(at(vector_prefix, b)) by { simp(); }
 apply(uint32_to_integer_bounds(old((uint32)self->a))) using {};
 apply(uint32_less_equal_to_integer(old((uint32)self->a), 65520u32)) using { old((uint32)self->a) <= 65520u32; };
 have (int32)(uint32)__rust_mir_138_remaining <= (int32)(uint32)bytes_len by { arithmetic() using { (int32)(uint32)__rust_mir_138_remaining == (int32)(uint32)remainder_len; (int32)(uint32)remainder_len <= (int32)(uint32)bytes_len; } }
 apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)bytes_len, (int32)(uint32)__rust_mir_138_remaining)) using { 0 <= (int32)(uint32)__rust_mir_138_remaining; (int32)(uint32)__rust_mir_138_remaining <= (int32)(uint32)bytes_len; };
 have ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) == (int32)(uint32)(bytes_len - bytes_len % 4u64) by { rewrite((int32)(uint32)__rust_mir_138_remaining == (int32)(uint32)remainder_len); assumption(); }
 have 0 <= old(to_integer((uint32)self->a)) by { assumption(); }
 have old(to_integer((uint32)self->a)) <= 65520 by { assumption(); }
 apply(uint32_to_integer_bounds(at(vector_prefix, b))) using {};
 have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining), old(to_integer((uint32)self->a))) by { rewrite(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) == (int32)(uint32)(bytes_len - bytes_len % 4u64)); rewrite(old(to_integer((uint32)self->a)) == to_integer(at(vector_prefix, a))); assumption(); }
 have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining), old(to_integer((uint32)self->a)), old(to_integer((uint32)self->b))) by { rewrite(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) == (int32)(uint32)(bytes_len - bytes_len % 4u64)); rewrite(old(to_integer((uint32)self->a)) == to_integer(at(vector_prefix, a))); rewrite(old(to_integer((uint32)self->b)) == to_integer(at(vector_prefix, b))); assumption(); }
 loop {
  decreases __rust_mir_138_remaining;
  views bytes[0..bytes_len];
  invariant bytes_len <= 22207u64;
  invariant bytes_len == old(bytes_len);
  invariant bytes == old(bytes);
  invariant 0 <= (int32)(uint32)remainder_len and (int32)(uint32)remainder_len <= 3;
  invariant (int32)(uint32)remainder_len <= (int32)(uint32)bytes_len;
  invariant 0 <= (int32)(uint32)bytes_len and (int32)(uint32)bytes_len <= 22207;
  invariant 0 <= (int32)(uint32)__rust_mir_138_remaining and (int32)(uint32)__rust_mir_138_remaining <= (int32)(uint32)remainder_len;
   invariant remainder_len <= 3u64;
   invariant remainder_len <= bytes_len;
   invariant __rust_mir_138_remaining <= remainder_len;
   invariant __rust_mir_138_cursor == bytes + (bytes_len - __rust_mir_138_remaining);
  invariant defined(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining));
  invariant 0 <= old(to_integer((uint32)self->a)) and old(to_integer((uint32)self->a)) <= 65520;
  invariant 0 <= old(to_integer((uint32)self->b));
  invariant truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining), old(to_integer((uint32)self->a)));
  invariant truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining), old(to_integer((uint32)self->a)), old(to_integer((uint32)self->b)));
  invariant 0 <= to_integer(a) and to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining));
  invariant 0 <= to_integer(b) and to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining));
  preserve by {
    have 0u64 < __rust_mir_138_remaining by { simp(); }
    have 1u64 <= __rust_mir_138_remaining by { arithmetic() using { 0u64 < __rust_mir_138_remaining; } }
    have __rust_mir_138_remaining <= 22208u64 by { arithmetic() using { __rust_mir_138_remaining <= remainder_len; remainder_len <= 3u64; } }
    apply(adler_count_tail_step(__rust_mir_138_remaining)) using { 1u64 <= __rust_mir_138_remaining; __rust_mir_138_remaining <= 22208u64; }
    have 0 < (int32)(uint32)__rust_mir_138_remaining by { arithmetic() using { 1 <= (int32)(uint32)__rust_mir_138_remaining; } }
   have 1 <= (int32)(uint32)__rust_mir_138_remaining by { arithmetic() using { 0 < (int32)(uint32)__rust_mir_138_remaining; } }
   have 0 <= (int32)(uint32)__rust_mir_138_remaining - 1 by { arithmetic() using { 0 < (int32)(uint32)__rust_mir_138_remaining; } }
   apply(int32_nonnegative_predecessor_upper_bound((int32)(uint32)__rust_mir_138_remaining, (int32)(uint32)remainder_len)) using { 0 <= (int32)(uint32)__rust_mir_138_remaining; (int32)(uint32)__rust_mir_138_remaining <= (int32)(uint32)remainder_len; }
   mark tail_head;
   have 1 <= at(tail_head, (int32)(uint32)__rust_mir_138_remaining) by { simp(); }
   have at(tail_head, (int32)(uint32)__rust_mir_138_remaining) <= (int32)(uint32)remainder_len by { simp(); }
   have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining))) by { simp(); }
   have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining))) by { simp(); }
    have 1u64 <= at(tail_head, __rust_mir_138_remaining) by { simp(); }
    have at(tail_head, __rust_mir_138_remaining) <= remainder_len by { simp(); }
    have at(tail_head, __rust_mir_138_cursor) == bytes + (bytes_len - at(tail_head, __rust_mir_138_remaining)) by { simp(); }
    have bytes_len - at(tail_head, __rust_mir_138_remaining) < bytes_len by { arithmetic() using { 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes_len; } }
   have truncating_remainder(to_integer(at(tail_head, a)), 65521) == adler_spec_a(bytes, ((int32)(uint32)bytes_len - at(tail_head, (int32)(uint32)__rust_mir_138_remaining)), old(to_integer((uint32)self->a))) by { simp(); }
   have truncating_remainder(to_integer(at(tail_head, b)), 65521) == adler_spec_b(bytes, ((int32)(uint32)bytes_len - at(tail_head, (int32)(uint32)__rust_mir_138_remaining)), old(to_integer((uint32)self->a)), old(to_integer((uint32)self->b))) by { simp(); }
   execute_until(assignment(byte, 0));
   have __rust_mir_155 == at(tail_head, __rust_mir_138_cursor) by { simp(); }
    have __rust_mir_155 == bytes + (bytes_len - at(tail_head, __rust_mir_138_remaining)) by { rewrite(__rust_mir_155 == at(tail_head, __rust_mir_138_cursor)); assumption(); }
   step();
   execute_until(assignment(__rust_mir_144, 0)); step();
   have __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64 by { simp(); }
   have (int32)(uint32)__rust_mir_138_remaining == at(tail_head, (int32)(uint32)__rust_mir_138_remaining) - 1 by { rewrite(__rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64); simp(); }
   have __rust_mir_138_remaining <= bytes_len by { arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes_len; } }
   have 1u64 <= bytes_len - __rust_mir_138_remaining by { arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes_len; } }
   have 0 <= (int32)(uint32)__rust_mir_138_remaining by { arithmetic() using { (int32)(uint32)__rust_mir_138_remaining == at(tail_head, (int32)(uint32)__rust_mir_138_remaining) - 1; 1 <= at(tail_head, (int32)(uint32)__rust_mir_138_remaining); at(tail_head, (int32)(uint32)__rust_mir_138_remaining) <= (int32)(uint32)remainder_len; (int32)(uint32)remainder_len <= (int32)(uint32)bytes_len; } }
   have (int32)(uint32)__rust_mir_138_remaining <= (int32)(uint32)bytes_len by { arithmetic() using { (int32)(uint32)__rust_mir_138_remaining == at(tail_head, (int32)(uint32)__rust_mir_138_remaining) - 1; 1 <= at(tail_head, (int32)(uint32)__rust_mir_138_remaining); at(tail_head, (int32)(uint32)__rust_mir_138_remaining) <= (int32)(uint32)remainder_len; (int32)(uint32)remainder_len <= (int32)(uint32)bytes_len; (int32)(uint32)bytes_len <= 22207; } }
   apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)bytes_len, (int32)(uint32)__rust_mir_138_remaining)) using { 0 <= (int32)(uint32)__rust_mir_138_remaining; (int32)(uint32)__rust_mir_138_remaining <= (int32)(uint32)bytes_len; };
   have 1 <= ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) by { arithmetic() using { (int32)(uint32)__rust_mir_138_remaining == at(tail_head, (int32)(uint32)__rust_mir_138_remaining) - 1; 1 <= at(tail_head, (int32)(uint32)__rust_mir_138_remaining); at(tail_head, (int32)(uint32)__rust_mir_138_remaining) <= (int32)(uint32)remainder_len; (int32)(uint32)remainder_len <= (int32)(uint32)bytes_len; (int32)(uint32)bytes_len <= 22207; } }
   apply(int32_nonnegative_subtract_within_value_is_defined(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining), 1)) using { 0 <= 1; 1 <= ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining); };
   have (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) == ((int32)(uint32)bytes_len - at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) by { arithmetic() using { (int32)(uint32)__rust_mir_138_remaining == at(tail_head, (int32)(uint32)__rust_mir_138_remaining) - 1; 1 <= at(tail_head, (int32)(uint32)__rust_mir_138_remaining); at(tail_head, (int32)(uint32)__rust_mir_138_remaining) <= (int32)(uint32)remainder_len; (int32)(uint32)remainder_len <= (int32)(uint32)bytes_len; (int32)(uint32)bytes_len <= 22207; } }
   have 0 <= (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) by { arithmetic() using { (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) == ((int32)(uint32)bytes_len - at(tail_head, (int32)(uint32)__rust_mir_138_remaining)); 1 <= at(tail_head, (int32)(uint32)__rust_mir_138_remaining); at(tail_head, (int32)(uint32)__rust_mir_138_remaining) <= (int32)(uint32)remainder_len; (int32)(uint32)remainder_len <= (int32)(uint32)bytes_len; (int32)(uint32)bytes_len <= 22207; } }
   have (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) <= 2147483646 by { arithmetic() using { (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) == ((int32)(uint32)bytes_len - at(tail_head, (int32)(uint32)__rust_mir_138_remaining)); 1 <= at(tail_head, (int32)(uint32)__rust_mir_138_remaining); at(tail_head, (int32)(uint32)__rust_mir_138_remaining) <= (int32)(uint32)remainder_len; (int32)(uint32)remainder_len <= (int32)(uint32)bytes_len; (int32)(uint32)bytes_len <= 22207; } }
   have ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) == (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) + 1 by { arithmetic() using { 0 <= (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1); (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) <= 2147483646; (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) == ((int32)(uint32)bytes_len - at(tail_head, (int32)(uint32)__rust_mir_138_remaining)); (int32)(uint32)__rust_mir_138_remaining == at(tail_head, (int32)(uint32)__rust_mir_138_remaining) - 1; 1 <= at(tail_head, (int32)(uint32)__rust_mir_138_remaining); at(tail_head, (int32)(uint32)__rust_mir_138_remaining) <= (int32)(uint32)remainder_len; (int32)(uint32)remainder_len <= (int32)(uint32)bytes_len; (int32)(uint32)bytes_len <= 22207; } }
   have bytes_len - __rust_mir_138_remaining - 1u64 == bytes_len - at(tail_head, __rust_mir_138_remaining) by { arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes_len; } }
   have __rust_mir_155 == bytes + (bytes_len - __rust_mir_138_remaining - 1u64) by { rewrite(bytes_len - __rust_mir_138_remaining - 1u64 == bytes_len - at(tail_head, __rust_mir_138_remaining)); assumption(); }
   apply(adler_count_previous_byte_observation(bytes, bytes_len, __rust_mir_138_remaining)) using { __rust_mir_138_remaining <= bytes_len; 1u64 <= bytes_len - __rust_mir_138_remaining; bytes_len <= 22207u64; 0 <= (int32)(uint32)__rust_mir_138_remaining; (int32)(uint32)__rust_mir_138_remaining <= (int32)(uint32)bytes_len; (int32)(uint32)bytes_len <= 22207; };
   have __rust_mir_144 == (uint32)__rust_mir_155[0] by { simp(); }
   apply(adler_helper_byte_observation(__rust_mir_155[0])) using {};
   have to_integer(__rust_mir_144) == to_integer((int32)(bytes + (bytes_len - __rust_mir_138_remaining - 1u64))[0]) by { rewrite(__rust_mir_144 == (uint32)__rust_mir_155[0]); rewrite(to_integer((uint32)__rust_mir_155[0]) == to_integer((int32)__rust_mir_155[0])); rewrite(__rust_mir_155 == bytes + (bytes_len - __rust_mir_138_remaining - 1u64)); normalize(); }
   have to_integer(__rust_mir_144) == to_integer((int32)bytes[(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1)]) by { rewrite(to_integer(__rust_mir_144) == to_integer((int32)(bytes + (bytes_len - __rust_mir_138_remaining - 1u64))[0])); assumption(); }
   have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1), old(to_integer((uint32)self->a))) by { rewrite((((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) == ((int32)(uint32)bytes_len - at(tail_head, (int32)(uint32)__rust_mir_138_remaining))); simp(); }
   have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1), old(to_integer((uint32)self->a)), old(to_integer((uint32)self->b))) by { rewrite((((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) == ((int32)(uint32)bytes_len - at(tail_head, (int32)(uint32)__rust_mir_138_remaining))); simp(); }
   apply(adler_prefix_a_step_one(bytes, (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1), old(to_integer((uint32)self->a)), to_integer(a))) using { 0 <= (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1); (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) <= 2147483646; 0 <= old(to_integer((uint32)self->a)); 0 <= to_integer(a); truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1), old(to_integer((uint32)self->a))); };
   apply(adler_prefix_b_step_one(bytes, (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1), old(to_integer((uint32)self->a)), old(to_integer((uint32)self->b)), to_integer(a), to_integer(b))) using { 0 <= (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1); (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) <= 2147483646; 0 <= old(to_integer((uint32)self->a)); old(to_integer((uint32)self->a)) <= 65520; 0 <= old(to_integer((uint32)self->b)); 0 <= to_integer(a); 0 <= to_integer(b); truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1), old(to_integer((uint32)self->a))); truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1), old(to_integer((uint32)self->a)), old(to_integer((uint32)self->b))); };
   have __rust_mir_144 <= 255u32 by { simp(); }
   apply(uint32_less_equal_to_integer(__rust_mir_144, 255u32)) using { __rust_mir_144 <= 255u32; }
   have to_integer(__rust_mir_144) <= 255 by { simp() using { to_integer(__rust_mir_144) <= to_integer(255u32); } }
   apply(adler_tail_iterator_step((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining), to_integer(a), to_integer(b), to_integer(__rust_mir_144))) using { 1 <= at(tail_head, (int32)(uint32)__rust_mir_138_remaining); (int32)(uint32)remainder_len <= 3; to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining))); to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining))); to_integer(__rust_mir_144) <= 255; }
   apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_144)) using { to_integer(a) + to_integer(__rust_mir_144) <= 4294967295; }
   execute_until(assignment(__rust_mir_146, 0));
   mark tail_add_a;
   have truncating_remainder(to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)), 65521) == adler_spec_a(bytes, ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining), old(to_integer((uint32)self->a))) by { rewrite(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) == (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) + 1); simp() using { truncating_remainder(to_integer(a) + to_integer((int32)bytes[(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1)]), 65521) == adler_spec_a(bytes, (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) + 1, old(to_integer((uint32)self->a))); to_integer(__rust_mir_144) == to_integer((int32)bytes[(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1)]); } }
   have truncating_remainder(to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)), 65521) == adler_spec_b(bytes, ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining), old(to_integer((uint32)self->a)), old(to_integer((uint32)self->b))) by { rewrite(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) == (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) + 1); simp() using { truncating_remainder(to_integer(b) + to_integer(a) + to_integer((int32)bytes[(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1)]), 65521) == adler_spec_b(bytes, (((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1) + 1, old(to_integer((uint32)self->a)), old(to_integer((uint32)self->b))); to_integer(__rust_mir_144) == to_integer((int32)bytes[(((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining) - 1)]); } }

   have to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) <= 4294967295 by { simp(); }
   step();
   have __rust_mir_146 == at(tail_add_a, a) + at(tail_add_a, __rust_mir_144) by { simp(); }
   apply(uint32_add_to_integer(at(tail_add_a, a), at(tail_add_a, __rust_mir_144))) using { to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) <= 4294967295; }
   have to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) by { rewrite(__rust_mir_146 == at(tail_add_a, a) + at(tail_add_a, __rust_mir_144)); assumption(); }
   have to_integer(__rust_mir_146) <= adler_tail_a_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1) by { simp() using { to_integer(a) + to_integer(__rust_mir_144) <= adler_tail_a_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1); to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); } }
   have to_integer(b) + to_integer(__rust_mir_146) <= 4294967295 by { simp() using { to_integer(b) + to_integer(a) + to_integer(__rust_mir_144) <= 4294967295; to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); } }
   have to_integer(b) + to_integer(__rust_mir_146) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1) by { simp() using { to_integer(b) + to_integer(a) + to_integer(__rust_mir_144) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1); to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); } }
   execute_until(assignment(a, 2)); step();
   have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1) by { simp(); }
   have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining), old(to_integer((uint32)self->a))) by { simp(); }
   execute_until(assignment(__rust_mir_147, 0)); step();
   have __rust_mir_147 == a by { simp(); }
   have a == __rust_mir_146 by { simp(); }
   have to_integer(b) + to_integer(__rust_mir_147) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1) by { rewrite(__rust_mir_147 == a); rewrite(a == __rust_mir_146); assumption(); }
   have to_integer(b) + to_integer(__rust_mir_147) <= 4294967295 by { simp(); }
   apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_147)) using { to_integer(b) + to_integer(__rust_mir_147) <= 4294967295; }
   execute_until(assignment(__rust_mir_148, 0));
   mark tail_add_b;
   have to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b)) by { simp(); }
   have to_integer(at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) by { simp(); }

   have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1) by { simp() using { to_integer(b) + to_integer(__rust_mir_147) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1); } }
   have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= 4294967295 by { simp(); }
   step();
   have __rust_mir_148 == at(tail_add_b, b) + at(tail_add_b, __rust_mir_147) by { simp(); }
   apply(uint32_add_to_integer(at(tail_add_b, b), at(tail_add_b, __rust_mir_147))) using { to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= 4294967295; }

   have to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) by { rewrite(__rust_mir_148 == at(tail_add_b, b) + at(tail_add_b, __rust_mir_147)); assumption(); }
   have to_integer(__rust_mir_148) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1) by { rewrite(to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147))); assumption(); }
   execute_until(assignment(b, 6)); step();
   have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1) by { simp(); }
   have to_integer(b) == to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) by { simp() using { to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)); to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b)); to_integer(at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); } }
   have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((int32)(uint32)bytes_len - (int32)(uint32)__rust_mir_138_remaining), old(to_integer((uint32)self->a)), old(to_integer((uint32)self->b))) by { rewrite(to_integer(b) == to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144))); assumption(); }
   execute_until(back_edge());
    have __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64 by { simp(); }
    have (int32)(uint32)__rust_mir_138_remaining == at(tail_head, (int32)(uint32)__rust_mir_138_remaining) - 1 by { rewrite(__rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64); simp(); }
   apply(adler_tail_remaining_progress((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining))) using { 1 <= at(tail_head, (int32)(uint32)__rust_mir_138_remaining); at(tail_head, (int32)(uint32)__rust_mir_138_remaining) <= (int32)(uint32)remainder_len; (int32)(uint32)remainder_len <= 3; }
   have adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining) == adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1 by { rewrite((int32)(uint32)__rust_mir_138_remaining == at(tail_head, (int32)(uint32)__rust_mir_138_remaining) - 1); assumption(); }
   have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining)) by { rewrite(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining) == adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1); assumption(); }
   have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining)) by { rewrite(adler_tail_consumed((int32)(uint32)remainder_len, (int32)(uint32)__rust_mir_138_remaining) == adler_tail_consumed((int32)(uint32)remainder_len, at(tail_head, (int32)(uint32)__rust_mir_138_remaining)) + 1); assumption(); }
   apply(uint32_to_integer_bounds(a)); apply(uint32_to_integer_bounds(b));
   have 0 <= (int32)(uint32)__rust_mir_138_remaining and (int32)(uint32)__rust_mir_138_remaining <= (int32)(uint32)remainder_len by { simp(); }
   have __rust_mir_138_cursor == at(tail_head, __rust_mir_138_cursor) + 1 by { simp(); }
    have __rust_mir_138_remaining <= remainder_len by { arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; } }
    have bytes_len - at(tail_head, __rust_mir_138_remaining) <= 18446744073709551614u64 by { arithmetic() using { 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes_len; } }
    have at(tail_head, __rust_mir_138_cursor) + 1 == bytes + ((bytes_len - at(tail_head, __rust_mir_138_remaining)) + 1u64) by { arithmetic() using { at(tail_head, __rust_mir_138_cursor) == bytes + (bytes_len - at(tail_head, __rust_mir_138_remaining)); bytes_len - at(tail_head, __rust_mir_138_remaining) <= 18446744073709551614u64; } }
    have bytes_len - __rust_mir_138_remaining == (bytes_len - at(tail_head, __rust_mir_138_remaining)) + 1u64 by { arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes_len; } }
    have __rust_mir_138_cursor == bytes + (bytes_len - __rust_mir_138_remaining) by { rewrite(bytes_len - __rust_mir_138_remaining == (bytes_len - at(tail_head, __rust_mir_138_remaining)) + 1u64); simp(); }
    have __rust_mir_138_remaining < at(tail_head, __rust_mir_138_remaining) by { arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); } }
   apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)bytes_len, (int32)(uint32)__rust_mir_138_remaining)) using { 0 <= (int32)(uint32)__rust_mir_138_remaining; (int32)(uint32)__rust_mir_138_remaining <= (int32)(uint32)bytes_len; };
   close_invariants by { simp(); }
  }
 }

 execute_until(assignment(__rust_mir_149, 0));
 have __rust_checked_34 == 65521u32 by { simp(); }
 step();
 have __rust_mir_149 == __rust_checked_32 % __rust_checked_34 by { simp() using {}; }
 have __rust_mir_149 == __rust_checked_32 % 65521u32 by { rewrite(__rust_mir_149 == __rust_checked_32 % __rust_checked_34); rewrite(__rust_checked_34 == 65521u32); normalize(); }
 apply(uint32_remainder_less_than_divisor(__rust_checked_32, 65521u32));
 have __rust_mir_149 < 65521u32 by { rewrite(__rust_mir_149 == __rust_checked_32 % 65521u32); assumption(); }
 apply(uint32_to_integer_bounds(__rust_mir_149));
 apply(uint32_less_than_to_integer(__rust_mir_149, 65521u32)) using { __rust_mir_149 < 65521u32; }
 have to_integer(__rust_mir_149) < 65521 by { simp() using { to_integer(__rust_mir_149) < to_integer(65521u32); } }
 have to_integer(__rust_mir_149) <= 65535 by { arithmetic() using { to_integer(__rust_mir_149) < 65521; } }
 mark small_reduced_a;
 execute_until(assignment(__rust_mir_151, 0));
 have __rust_checked_37 == 65521u32 by { simp(); }
 step();
 have __rust_mir_151 == __rust_checked_35 % __rust_checked_37 by { simp() using {}; }
 have __rust_mir_151 == __rust_checked_35 % 65521u32 by { rewrite(__rust_mir_151 == __rust_checked_35 % __rust_checked_37); rewrite(__rust_checked_37 == 65521u32); normalize(); }
 apply(uint32_remainder_less_than_divisor(__rust_checked_35, 65521u32));
 have __rust_mir_151 < 65521u32 by { rewrite(__rust_mir_151 == __rust_checked_35 % 65521u32); assumption(); }
 apply(uint32_to_integer_bounds(__rust_mir_151));
 apply(uint32_less_than_to_integer(__rust_mir_151, 65521u32)) using { __rust_mir_151 < 65521u32; }
 have to_integer(__rust_mir_151) < 65521 by { simp() using { to_integer(__rust_mir_151) < to_integer(65521u32); } }
 have to_integer(__rust_mir_151) <= 65535 by { arithmetic() using { to_integer(__rust_mir_151) < 65521; } }
 mark small_reduced_b;
 execute();
 have to_integer(self->a) == to_integer(at(small_reduced_a, __rust_mir_149)) by { arithmetic_certificate special {
 premise 0: 0 <= to_integer(at(small_reduced_a, __rust_mir_149)) => 0 <= to_integer(at(small_reduced_a, __rust_mir_149));
 premise 1: to_integer(at(small_reduced_a, __rust_mir_149)) <= 65535 => to_integer(at(small_reduced_a, __rust_mir_149)) <= 65535;
 integer_cast_identity bounds [0, 1] => to_integer(self->a) == to_integer(at(small_reduced_a, __rust_mir_149)); conclusion 0;
 } }
 have to_integer(at(small_reduced_a, __rust_mir_149)) < 65521 by { simp(); }
 have to_integer(self->a) < 65521 by { rewrite(to_integer(self->a) == to_integer(at(small_reduced_a, __rust_mir_149))); assumption(); }
 have to_integer(self->b) == to_integer(at(small_reduced_b, __rust_mir_151)) by { arithmetic_certificate special {
 premise 0: 0 <= to_integer(at(small_reduced_b, __rust_mir_151)) => 0 <= to_integer(at(small_reduced_b, __rust_mir_151));
 premise 1: to_integer(at(small_reduced_b, __rust_mir_151)) <= 65535 => to_integer(at(small_reduced_b, __rust_mir_151)) <= 65535;
 integer_cast_identity bounds [0, 1] => to_integer(self->b) == to_integer(at(small_reduced_b, __rust_mir_151)); conclusion 0;
 } }
 have to_integer(at(small_reduced_b, __rust_mir_151)) < 65521 by { simp(); }
 have to_integer(self->b) < 65521 by { rewrite(to_integer(self->b) == to_integer(at(small_reduced_b, __rust_mir_151))); assumption(); }
 have 0 <= to_integer(self->a) by { rewrite(to_integer(self->a) == to_integer(at(small_reduced_a, __rust_mir_149))); simp() using { 0 <= to_integer(at(small_reduced_a, __rust_mir_149)); } }
 have to_integer(self->a) <= 65535 by { arithmetic() using { to_integer(self->a) < 65521; } }
 have to_integer((int32)self->a) == to_integer(self->a) by { arithmetic_certificate special {
 premise 0: 0 <= to_integer(self->a) => 0 <= to_integer(self->a);
 premise 1: to_integer(self->a) <= 65535 => to_integer(self->a) <= 65535;
 integer_cast_identity bounds [0, 1] => to_integer((int32)self->a) == to_integer(self->a); conclusion 0;
 } }
 have to_integer((int32)self->a) <= to_integer(65520) by { rewrite(to_integer((int32)self->a) == to_integer(self->a)); arithmetic() using { to_integer(self->a) < 65521; } }
 apply(int32_less_equal_of_to_integer((int32)self->a, 65520)) using { to_integer((int32)self->a) <= to_integer(65520); }
 apply(adler_i32_below_mod((int32)self->a)) using { (int32)self->a <= 65520; }
 have self->a < 65521 by { assumption(); }
 have 0 <= to_integer(self->b) by { rewrite(to_integer(self->b) == to_integer(at(small_reduced_b, __rust_mir_151))); simp() using { 0 <= to_integer(at(small_reduced_b, __rust_mir_151)); } }
 have to_integer(self->b) <= 65535 by { arithmetic() using { to_integer(self->b) < 65521; } }
 have to_integer((int32)self->b) == to_integer(self->b) by { arithmetic_certificate special {
 premise 0: 0 <= to_integer(self->b) => 0 <= to_integer(self->b);
 premise 1: to_integer(self->b) <= 65535 => to_integer(self->b) <= 65535;
 integer_cast_identity bounds [0, 1] => to_integer((int32)self->b) == to_integer(self->b); conclusion 0;
 } }
 have to_integer((int32)self->b) <= to_integer(65520) by { rewrite(to_integer((int32)self->b) == to_integer(self->b)); arithmetic() using { to_integer(self->b) < 65521; } }
 apply(int32_less_equal_of_to_integer((int32)self->b, 65520)) using { to_integer((int32)self->b) <= to_integer(65520); }
 apply(adler_i32_below_mod((int32)self->b)) using { (int32)self->b <= 65520; }
 have self->b < 65521 by { assumption(); }
 simp() using { self->a < 65521; self->b < 65521; }
}
