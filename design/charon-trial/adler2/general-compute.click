// Whole-body checksum correctness, bounds and termination for unchanged Adler32::compute.
// Canonical seeds and every input length through the signed observation limit.
// The harness checks the helper bodies and assembles their arithmetic libraries.
// The full-batch loops carry both residues against the common specification.
// Aligned-remainder constructors carry exact absolute input-byte observations.
// The aligned remainder carries both residues through its actual lane-loop exit.
// Original remainder reductions and recombination preserve both residues.
// The original scalar tail and final fields satisfy the common entry-input specification.

theorem adler_uint64_self_subtract(n: uint64) { ensures n - n == 0u64 by normalize(); }
theorem adler_i32_below_mod(n: int32) { requires n <= 65520; ensures n < 65521 by arithmetic() using { n <= 65520; }; }
theorem adler_bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22204;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by simp() using { 0 <= index; index <= 22204; };
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
  apply(uint64_less_equal_to_integer(0u64, length)) using { 0u64 <= length; }
  apply(uint64_less_equal_to_integer(length, 22204u64)) using { length <= 22204u64; }
  have 0 <= to_integer(length) by assumption();
  have to_integer(length) <= 4294967295 by arithmetic() using { to_integer(length) <= 22204; };
  have to_integer((length as u32)) == to_integer(length) by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer(length) => 0 <= to_integer(length);
    premise 1: to_integer(length) <= 4294967295 => to_integer(length) <= 4294967295;
    integer_cast_identity bounds [0, 1] => to_integer((length as u32)) == to_integer(length);
    conclusion 0;
   }
  }
  have to_integer((length as u32)) <= to_integer(22204u32) by { rewrite(to_integer((length as u32)) == to_integer(length)); assumption(); }
  apply(uint32_to_integer_less_equal_implies_less_equal((length as u32), 22204u32)) using { to_integer((length as u32)) <= to_integer(22204u32); }
 }
}



theorem adler_tail_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 2147483646;
 ensures (base + index) + 1 == base + (index + 1) by {
  have defined(index + 1) by simp() using { 0 <= index; index <= 2147483646; };
  normalize() using { defined(index + 1); }
 }
}

impl adler2::Adler32 {
    fn compute(&mut self, bytes: &[u8]) {
     requires bytes.len() <= 2147483647u64;
     requires (self.a as u32) <= 65520u32;
     requires (self.b as u32) <= 65520u32;
     owns self.a; owns self.b; views *bytes;
     ensures self.a < 65521;
     ensures self.b < 65521;
     ensures to_integer(self.a) <= 65520;
     ensures to_integer(self.b) <= 65520;
     ensures to_integer(self.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))));
     ensures to_integer(self.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
    } by {
     apply(adler_general_signed_bounded_prefix(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_general_native_bounded_prefix_divisible(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_general_bounded_native_prefix(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_general_bounded_tail_metadata(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_general_bounded_signed_tail(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_general_signed_partition_identity(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_outer_remainder_native_bound(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; }
     apply(adler_outer_remainder_signed_divisible(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; }
     apply(adler_outer_bulk_signed(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; }
     apply(adler_outer_bulk_signed_multiple(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; }
     have bytes.len() % 4u64 <= bytes.len() by normalize();
     apply(adler_outer_bulk_within_prefix(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; }
     apply(adler_general_bounded_prefix_within_full(bytes.len())) using { bytes.len() <= 2147483647u64; }
     execute_until(assignment(b, 0)); step();
     have a <= 65520u32;
     have b <= 65520u32;
     execute_until(loop(0));
     have __rust_mir_27_remaining == ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
     apply(adler_outer_bulk_observation(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; }
     have to_integer(__rust_mir_27_remaining) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) by { rewrite(__rust_mir_27_remaining == ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); simp(); }
     have to_integer(__rust_mir_27_remaining) <= to_integer(2147483647u64) by arithmetic() using { to_integer(__rust_mir_27_remaining) == to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); to_integer(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)) <= 2147483644; };
     have __rust_mir_27_remaining <= 2147483647u64 by { apply(uint64_to_integer_less_equal_implies_less_equal(__rust_mir_27_remaining, 2147483647u64)); assumption(); }
     apply(adler_bounded_count(__rust_mir_27_remaining));
     have (((__rust_mir_27_remaining as u32) as i32)) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32);
     have __rust_mir_27_cursor == old(bytes);
     have __rust_mir_27_size == 22208u64;
     have 0 <= (((__rust_mir_27_remaining as u32) as i32)) by { rewrite((((__rust_mir_27_remaining as u32) as i32)) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); assumption(); }
     have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by simp() using { bytes.len() == old(bytes.len()); };
     have (((__rust_mir_27_remaining as u32) as i32)) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by { rewrite((((__rust_mir_27_remaining as u32) as i32)) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); normalize() using {}; }
     have (((__rust_mir_27_remaining as u32) as i32)) % 22208 == 0 by { rewrite((((__rust_mir_27_remaining as u32) as i32)) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); assumption(); }
     have __rust_mir_27_cursor == old(bytes) + (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - (((__rust_mir_27_remaining as u32) as i32))) by { rewrite((((__rust_mir_27_remaining as u32) as i32)) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); rewrite(__rust_mir_27_cursor == old(bytes)); normalize() using {}; }
     have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
     have remainder_len == bytes.len() % 4u64;
     have bytes == old(bytes) by assumption();
     have bytes.len() == old(bytes.len()) by assumption();
     have to_integer(a_vec.0[0]) <= 65520;
     have to_integer(a_vec.0[1]) <= 65520;
     have to_integer(a_vec.0[2]) <= 65520;
     have to_integer(a_vec.0[3]) <= 65520;
     have to_integer(b_vec.0[0]) <= 65520;
     have to_integer(b_vec.0[1]) <= 65520;
     have to_integer(b_vec.0[2]) <= 65520;
     have to_integer(b_vec.0[3]) <= 65520;
     apply(adler_general_index_observation(bytes.len())) using { bytes.len() <= 2147483647u64; }
     have 0 <= ((bytes.len() as u32) as i32);
     have __rust_mir_33_live == 0;
     have __rust_mir_34_live == 0;
     have __rust_mir_36_live == 0;
     have 0 <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); assumption(); }
     have old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) <= (((bytes.len() - bytes.len() % 4u64) as u32) as i32) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); assumption(); }
     have old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) <= ((bytes.len() as u32) as i32) by arithmetic() using { old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) <= (((bytes.len() - bytes.len() % 4u64) as u32) as i32); (((bytes.len() - bytes.len() % 4u64) as u32) as i32) <= ((bytes.len() as u32) as i32); };
     have __rust_checked_92 == old(bytes);
     have __rust_checked_93 == bytes.len() - bytes.len() % 4u64;
     have __rust_checked_94 == 22208u64;
     have remainder_chunk == __rust_checked_92 + (__rust_checked_93 - __rust_checked_93 % __rust_checked_94);
     have __rust_checked_93 - __rust_checked_93 % __rust_checked_94 == __rust_mir_27_remaining;
     have __rust_checked_93 - __rust_checked_93 % __rust_checked_94 <= 2147483647u64 by { rewrite(__rust_checked_93 - __rust_checked_93 % __rust_checked_94 == __rust_mir_27_remaining); assumption(); }
     apply(adler_bounded_pointer_index(__rust_checked_92, __rust_checked_93 - __rust_checked_93 % __rust_checked_94));
     have remainder_chunk == __rust_checked_92 + (((__rust_checked_93 - __rust_checked_93 % __rust_checked_94) as u32) as i32) by {
      rewrite(remainder_chunk == __rust_checked_92 + (__rust_checked_93 - __rust_checked_93 % __rust_checked_94));
      assumption();
     }
     have remainder_chunk == old(bytes) + old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by {
      rewrite(remainder_chunk == __rust_checked_92 + (((__rust_checked_93 - __rust_checked_93 % __rust_checked_94) as u32) as i32));
      rewrite(__rust_checked_92 == old(bytes));
      rewrite(__rust_checked_93 == bytes.len() - bytes.len() % 4u64);
      rewrite(__rust_checked_94 == 22208u64);
      rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)));
      normalize();
     }


     have (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64) by normalize();
     have ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= (bytes.len() - bytes.len() % 4u64) by normalize() using { (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64); };
     have ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= bytes.len() by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64);  ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= (bytes.len() - bytes.len() % 4u64); (bytes.len() - bytes.len() % 4u64) <= bytes.len(); };
     have __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) by { rewrite(__rust_mir_27_remaining == ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); normalize(); }
     apply(adler_uint64_self_subtract(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)));
     have __rust_mir_27_cursor == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) by {
      rewrite(__rust_mir_27_remaining == ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64));
      rewrite(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) == 0u64);
      rewrite(__rust_mir_27_cursor == old(bytes)); rewrite(bytes == old(bytes)); normalize();
     }
     // Establish the empty original-input prefix before the full-batch loop.
     apply(uint32_to_integer_bounds(a)) using {};
     apply(uint32_less_equal_to_integer(a, 65520u32)) using { a <= 65520u32; }
     apply(adler_spec_empty(bytes, to_integer(a), 0)) using { 0 <= to_integer(a); to_integer(a) <= 65520; 0 <= 0; 0 <= 65520; }
     have to_integer(a_vec.0[0]) == 0;
     have to_integer(a_vec.0[1]) == 0;
     have to_integer(a_vec.0[2]) == 0;
     have to_integer(a_vec.0[3]) == 0;
     have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)) == 0 by { rewrite(((__rust_mir_27_remaining as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); normalize(); }
     have adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) == to_integer(a) by { unfold(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); arithmetic() using { to_integer(a_vec.0[0]) == 0; to_integer(a_vec.0[1]) == 0; to_integer(a_vec.0[2]) == 0; to_integer(a_vec.0[3]) == 0; } }
     have to_integer(a) == 0 * 65521 + to_integer(a) by arithmetic() using {};
     apply(adler_residue_unique(to_integer(a), 0, to_integer(a))) using { 0 <= to_integer(a); to_integer(a) == 0 * 65521 + to_integer(a); to_integer(a) <= 65520; };
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(a)) by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)) == 0); rewrite(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) == to_integer(a)); arithmetic() using { truncating_remainder(to_integer(a), 65521) == to_integer(a); adler_spec_a(bytes, 0, to_integer(a)) == to_integer(a); } }
     // Keep the entry B seed fixed while the working scalar B is reduced.
     apply(uint32_to_integer_bounds(b)) using {};
     apply(uint32_less_equal_to_integer(b, 65520u32)) using { b <= 65520u32; }
     have to_integer(b) == old(to_integer((self.b as u32))) by simp();
     have 0 <= old(to_integer((self.b as u32))) by arithmetic() using { 0 <= to_integer(b); to_integer(b) == old(to_integer((self.b as u32))); };
     have old(to_integer((self.b as u32))) <= 65520 by arithmetic() using { to_integer(b) <= 65520; to_integer(b) == old(to_integer((self.b as u32))); };
     apply(adler_spec_empty(bytes, to_integer(a), old(to_integer((self.b as u32))))) using { 0 <= to_integer(a); to_integer(a) <= 65520; 0 <= old(to_integer((self.b as u32))); old(to_integer((self.b as u32))) <= 65520; }
     have to_integer(b_vec.0[0]) == 0;
     have to_integer(b_vec.0[1]) == 0;
     have to_integer(b_vec.0[2]) == 0;
     have to_integer(b_vec.0[3]) == 0;
     apply(adler_zero_lane_b_residue(to_integer(b))) using { 0 <= to_integer(b); to_integer(b) <= 65520; }
     have adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) == adler_lane_b(to_integer(b), 0, 0, 0, 0, 0, 0, 0) by {
      rewrite(to_integer(a_vec.0[1]) == 0);
      rewrite(to_integer(a_vec.0[2]) == 0);
      rewrite(to_integer(a_vec.0[3]) == 0);
      rewrite(to_integer(b_vec.0[0]) == 0);
      rewrite(to_integer(b_vec.0[1]) == 0);
      rewrite(to_integer(b_vec.0[2]) == 0);
      rewrite(to_integer(b_vec.0[3]) == 0);
      normalize();
     }
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)) == 0); rewrite(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) == adler_lane_b(to_integer(b), 0, 0, 0, 0, 0, 0, 0)); arithmetic() using { truncating_remainder(adler_lane_b(to_integer(b), 0, 0, 0, 0, 0, 0, 0), 65521) == to_integer(b); adler_spec_b(bytes, 0, to_integer(a), old(to_integer((self.b as u32)))) == old(to_integer((self.b as u32))); to_integer(b) == old(to_integer((self.b as u32))); }; }
     loop {
     decreases (((__rust_mir_27_remaining as u32) as i32));
     invariant __rust_mir_27_remaining <= 2147483647u64;
     invariant ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= bytes.len();
     invariant __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
     invariant __rust_mir_27_cursor == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining);
     owns a_vec.0[0..4]; owns b_vec.0[0..4];
     views *bytes;
     invariant bytes == old(bytes);
     invariant forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) };
     invariant bytes.len() == old(bytes.len());
     invariant bytes.len() <= 2147483647u64;
     invariant 0 <= ((bytes.len() as u32) as i32);
     invariant a <= 65520u32;
     invariant b <= 65520u32;
     invariant __rust_mir_27_size == 22208u64;
     invariant __rust_mir_33_live == 0;
     invariant __rust_mir_34_live == 0;
     invariant __rust_mir_36_live == 0;

     invariant 0 <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32));
     invariant old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) <= ((bytes.len() as u32) as i32);
     invariant ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32));
     invariant 0 <= (((__rust_mir_27_remaining as u32) as i32));
     invariant (((__rust_mir_27_remaining as u32) as i32)) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32));
     invariant (((__rust_mir_27_remaining as u32) as i32)) % 22208 == 0;
     invariant __rust_mir_27_cursor == old(bytes) + (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - (((__rust_mir_27_remaining as u32) as i32)));
     invariant remainder_chunk == old(bytes) + old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32));
     invariant __rust_checked_93 == bytes.len() - bytes.len() % 4u64;
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
     invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(a));
     invariant 0 <= old(to_integer((self.b as u32)));
     invariant truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(a), old(to_integer((self.b as u32))));
     preserve by {
      have 0 < (((__rust_mir_27_remaining as u32) as i32));
      apply(adler_outer_nonempty_remaining((((__rust_mir_27_remaining as u32) as i32)))) using { 0 < (((__rust_mir_27_remaining as u32) as i32)); (((__rust_mir_27_remaining as u32) as i32)) % 22208 == 0; }
      mark outer_head;
      have at(outer_head, __rust_mir_27_remaining) <= 2147483647u64;
      have at(outer_head, __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
      have at(outer_head, __rust_mir_27_cursor) == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining));
      have at(outer_head, __rust_mir_27_cursor) == old(bytes) + (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32))));
      execute_until(loop(1));
      have chunk_len == 22208u64;

      have chunk == at(outer_head, __rust_mir_27_cursor);
      have (((__rust_mir_27_remaining as u32) as i32)) == at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208;
      have __rust_mir_36_remaining == 22208u64 by { rewrite(chunk_len == 22208u64); normalize(); }
     have (((__rust_mir_36_remaining as u32) as i32)) == 22208 by { rewrite(__rust_mir_36_remaining == 22208u64); normalize(); }
      have __rust_mir_36_cursor == chunk;
      have 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32)));
     have __rust_mir_27_remaining == at(outer_head, __rust_mir_27_remaining) - 22208u64;
     apply(adler_bounded_count_native_lower(at(outer_head, __rust_mir_27_remaining), 22208)) using {
      at(outer_head, __rust_mir_27_remaining) <= 2147483647u64;
      0 <= 22208;
      22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32)));
     }
     have at(outer_head, __rust_mir_27_remaining) <= 2147483647u64;
     have __rust_mir_27_remaining <= 2147483647u64 by arithmetic() using {
      __rust_mir_27_remaining == at(outer_head, __rust_mir_27_remaining) - 22208u64;
      22208u64 <= at(outer_head, __rust_mir_27_remaining);
      at(outer_head, __rust_mir_27_remaining) <= 2147483647u64;
     };

      have __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64);
       __rust_mir_27_remaining == at(outer_head, __rust_mir_27_remaining) - 22208u64;
       22208u64 <= at(outer_head, __rust_mir_27_remaining);
       at(outer_head, __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
      };
      have ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining) <= bytes.len() by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64);  at(outer_head, __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= bytes.len(); };
      have 22208u64 <= bytes.len() - (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64);
       22208u64 <= at(outer_head, __rust_mir_27_remaining);
       at(outer_head, __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= bytes.len();
      };
      have chunk == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) by { rewrite(chunk == at(outer_head, __rust_mir_27_cursor)); assumption(); }
      have 22208u64 <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64);
       __rust_mir_27_remaining == at(outer_head, __rust_mir_27_remaining) - 22208u64;
       at(outer_head, __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
       22208u64 <= at(outer_head, __rust_mir_27_remaining);
       __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
      };
      have (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64) == (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64);
       __rust_mir_27_remaining == at(outer_head, __rust_mir_27_remaining) - 22208u64;
       at(outer_head, __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
       22208u64 <= at(outer_head, __rust_mir_27_remaining);
       __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
       22208u64 <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining;
      };
      have chunk == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64) by { rewrite((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64) == (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining))); assumption(); }
      have (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64) <= bytes.len() by { rewrite((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64) == (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining))); assumption(); }
      have 22208u64 <= bytes.len() - (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64) by { rewrite((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64) == (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining))); assumption(); }
      have at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32));
      have 0 <= (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) by arithmetic() using { at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))); };
      have 0 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) by arithmetic() using { 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))); };
      have defined(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) by apply(int32_nonnegative_subtract_within_value_is_defined(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)), at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))) using { 0 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))); at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); };
      have (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) <= 2147461439 by arithmetic() using { at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))); defined(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))); };
      have defined((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208) by { apply(int32_nonnegative_add_within_max_is_defined((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))), 22208)) using { 0 <= 22208; (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) <= 2147483647 - 22208; } simp(); }
      have (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208 <= ((bytes.len() as u32) as i32) by arithmetic() using { old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) <= ((bytes.len() as u32) as i32); 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))); at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); defined(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))); defined((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208); };
      have (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) <= (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208 by arithmetic() using { at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))); 0 <= (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))); (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) <= 2147461439; defined(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))); defined((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208); };
      have chunk == bytes + (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) by { rewrite(chunk == at(outer_head, __rust_mir_27_cursor)); rewrite(at(outer_head, __rust_mir_27_cursor) == old(bytes) + (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))); rewrite(bytes == old(bytes)); normalize() using {}; }
      apply(adler_outer_remaining_step(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)), at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))) using { 0 <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))); }
      have 0 <= (((__rust_mir_27_remaining as u32) as i32)) by { rewrite((((__rust_mir_27_remaining as u32) as i32)) == at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208); assumption(); }
      have (((__rust_mir_27_remaining as u32) as i32)) <= ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); rewrite((((__rust_mir_27_remaining as u32) as i32)) == at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208); assumption(); }
      have defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32))) by apply(int32_nonnegative_subtract_within_value_is_defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), (((__rust_mir_27_remaining as u32) as i32)))) using { 0 <= (((__rust_mir_27_remaining as u32) as i32)); (((__rust_mir_27_remaining as u32) as i32)) <= ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32); };
      apply(int32_subtract_to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), (((__rust_mir_27_remaining as u32) as i32)))) using { defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32))); }
      apply(int32_subtract_to_integer(at(outer_head, (((__rust_mir_27_remaining as u32) as i32))), 22208)) using { defined(at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208); }
      apply(int32_less_equal_to_integer(at(outer_head, (((__rust_mir_27_remaining as u32) as i32))), old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)))) using { at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); }
      have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) == to_integer(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); normalize() using {}; }
      have to_integer((((__rust_mir_27_remaining as u32) as i32))) == to_integer(at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) - 22208 by { rewrite((((__rust_mir_27_remaining as u32) as i32)) == at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208); assumption(); }
      have 22208 <= to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32))) by arithmetic() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - to_integer((((__rust_mir_27_remaining as u32) as i32))); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) == to_integer(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); to_integer((((__rust_mir_27_remaining as u32) as i32))) == to_integer(at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) - 22208; to_integer(at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) <= to_integer(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); };
      apply(int32_to_integer_less_equal_implies_less_equal(22208, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)))) using { 22208 <= to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32))); }
      have defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) by { apply(int32_nonnegative_subtract_within_value_is_defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)), 22208)) using { 0 <= 22208; 22208 <= ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)); } simp(); }
      apply(int32_subtract_to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)), 22208)) using { defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208); }
      apply(int32_subtract_to_integer(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)), at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))) using { defined(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))); }
      have to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) == to_integer((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))) by arithmetic() using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32))) - to_integer(22208); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32))) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - to_integer((((__rust_mir_27_remaining as u32) as i32))); to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) == to_integer(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); to_integer((((__rust_mir_27_remaining as u32) as i32))) == to_integer(at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) - 22208; to_integer(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) == to_integer(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))) - to_integer(at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))); };
      have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) == (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) by apply(int32_to_integer_equal_implies_equal((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208), (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))))) using { to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) == to_integer((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))); };
      have 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) == (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))); assumption(); }
      have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439 by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) == (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))); assumption(); }
      have defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208) by { apply(int32_nonnegative_add_within_max_is_defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208), 22208)) using { 0 <= 22208; (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147483647 - 22208; } simp(); }
      apply(int32_add_to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208), 22208)) using { defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208); }
      apply(int32_add_to_integer((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))), 22208)) using { defined((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208); }
      have to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208) == to_integer((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208) by arithmetic() using { to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208) == to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + to_integer(22208); to_integer((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208) == to_integer((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))) + to_integer(22208); to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) == to_integer((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))); };
      have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208 == (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208 by apply(int32_to_integer_equal_implies_equal((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208, (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208)) using { to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208) == to_integer((old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208); };
      have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208 <= ((bytes.len() as u32) as i32) by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208 == (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))) + 22208); assumption(); }
      have to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) <= to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208) by arithmetic() using { to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208) == to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + to_integer(22208); };
      have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208 by apply(int32_to_integer_less_equal_implies_less_equal((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208)) using { to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) <= to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208); };
      have chunk == bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) == (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))); assumption(); }
      mark outer_chunk;
      have ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))) == (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, ((__rust_mir_27_remaining as u32) as i32))) by {
       rewrite(((__rust_mir_36_remaining as u32) as i32) == 22208);
       rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) == (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, ((__rust_mir_27_remaining as u32) as i32))));
       normalize();
      }
      have defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208)) by assumption();
      apply(adler_defined_add_zero((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208))) using {};
      have defined(((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32)))) by {
       rewrite(((__rust_mir_36_remaining as u32) as i32) == 22208);
       both { assumption(); } and { both { normalize(); } and { assumption(); } }
      }
      have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))), to_integer(a)) by {
       rewrite(((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))) == (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, ((__rust_mir_27_remaining as u32) as i32))));
       simp();
      }
      have __rust_mir_36_size == 4u64;
      have chunk == at(outer_chunk, chunk);
      have __rust_mir_36_live == 1;
      have (((__rust_mir_27_remaining as u32) as i32)) == at(outer_chunk, (((__rust_mir_27_remaining as u32) as i32)));
      have __rust_mir_27_cursor == at(outer_chunk, __rust_mir_27_cursor);
     apply(adler_lane_initial_ceiling());
     apply(adler_lane_iterator_initial(22208));
     have adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))) == 0 by { rewrite((((__rust_mir_36_remaining as u32) as i32)) == 22208); assumption(); }
     have to_integer(a_vec.0[0]) <= 65520;
     have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec.0[0]) <= 65520; } }
     have to_integer(b_vec.0[0]) <= 65520;
     have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec.0[0]) <= 65520; } }
     have to_integer(a_vec.0[1]) <= 65520;
     have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec.0[1]) <= 65520; } }
     have to_integer(b_vec.0[1]) <= 65520;
     have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec.0[1]) <= 65520; } }
     have to_integer(a_vec.0[2]) <= 65520;
     have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec.0[2]) <= 65520; } }
     have to_integer(b_vec.0[2]) <= 65520;
     have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec.0[2]) <= 65520; } }
     have to_integer(a_vec.0[3]) <= 65520;
     have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec.0[3]) <= 65520; } }
     have to_integer(b_vec.0[3]) <= 65520;
     have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec.0[3]) <= 65520; } }
     have 0 <= (((__rust_mir_36_remaining as u32) as i32)) by { rewrite((((__rust_mir_36_remaining as u32) as i32)) == 22208); normalize() using {}; }
     have (((__rust_mir_36_remaining as u32) as i32)) <= 22208 by { rewrite((((__rust_mir_36_remaining as u32) as i32)) == 22208); normalize() using {}; }
     have 0 <= (((__rust_mir_36_remaining as u32) as i32)) and (((__rust_mir_36_remaining as u32) as i32)) <= 22208 by assumption();
     have (((__rust_mir_36_remaining as u32) as i32)) % 4 == 0 by { rewrite((((__rust_mir_36_remaining as u32) as i32)) == 22208); normalize() using {}; }
     have __rust_mir_36_cursor == at(outer_chunk, chunk) + (22208 - (((__rust_mir_36_remaining as u32) as i32))) by { rewrite((((__rust_mir_36_remaining as u32) as i32)) == 22208); simp(); }
     have chunk_len < 22209u64;
     have chunk_len == 22208u64 by assumption();
     simp();
     have __rust_mir_36_remaining <= 22208u64;
     have __rust_mir_36_cursor == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - __rust_mir_36_remaining) by {
      rewrite(__rust_mir_36_cursor == chunk);
      rewrite(__rust_mir_36_remaining == 22208u64);
      rewrite(chunk == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64)); normalize();
     }
     have (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; at(outer_head, __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); };
     have (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) <= bytes.len() by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; at(outer_head, __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= bytes.len(); };
     have (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) <= 18446744073709529407u64 by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; at(outer_head, __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) <= bytes.len(); bytes.len() <= 2147483647u64; };
     have __rust_mir_27_cursor == at(outer_head, __rust_mir_27_cursor) + 22208;
     have at(outer_head, __rust_mir_27_cursor) + 22208 == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) + 22208u64) by arithmetic() using { at(outer_head, __rust_mir_27_cursor) == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)); (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) <= 18446744073709529407u64; };
     have (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) == (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) + 22208u64 by arithmetic() using { __rust_mir_27_remaining == at(outer_head, __rust_mir_27_remaining) - 22208u64; 22208u64 <= at(outer_head, __rust_mir_27_remaining); bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; at(outer_head, __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); };
     have __rust_mir_27_cursor == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) by { rewrite((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) == (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - at(outer_head, __rust_mir_27_remaining)) + 22208u64); simp(); }
     // B keeps the batch-local scalar contribution deferred until Rust adds it.
     apply(uint32_to_integer_bounds(b)) using {};
     apply(uint32_to_integer_bounds(b_vec.0[0])) using {};
     apply(uint32_to_integer_bounds(b_vec.0[1])) using {};
     apply(uint32_to_integer_bounds(b_vec.0[2])) using {};
     apply(uint32_to_integer_bounds(b_vec.0[3])) using {};
     apply(adler_canonical_lane_b_floor(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]))) using { 0 <= to_integer(b); to_integer(a_vec.0[1]) <= 65520; to_integer(a_vec.0[2]) <= 65520; to_integer(a_vec.0[3]) <= 65520; 0 <= to_integer(b_vec.0[0]); 0 <= to_integer(b_vec.0[1]); 0 <= to_integer(b_vec.0[2]); 0 <= to_integer(b_vec.0[3]); }
     have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { apply(adler_empty_full_batch_position(((__rust_mir_36_remaining as u32) as i32))) using { ((__rust_mir_36_remaining as u32) as i32) == 22208; } rewrite(to_integer(22208 - ((__rust_mir_36_remaining as u32) as i32)) == 0); simp(); }
     apply(adler_empty_full_batch_position(((__rust_mir_36_remaining as u32) as i32))) using { ((__rust_mir_36_remaining as u32) as i32) == 22208; }
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))) == (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, ((__rust_mir_27_remaining as u32) as i32)))); rewrite(to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) == 0); simp(); }
     loop {
      decreases (((__rust_mir_36_remaining as u32) as i32));
     invariant __rust_mir_36_remaining <= 22208u64;
     invariant __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
     invariant ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= bytes.len();
     invariant __rust_mir_27_remaining <= 2147483647u64;
      owns a_vec.0[0..4];
      owns b_vec.0[0..4];
      views *bytes;
      invariant __rust_mir_27_cursor == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining);
      invariant __rust_mir_36_cursor == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - __rust_mir_36_remaining);
      invariant __rust_mir_36_remaining <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining);
      invariant chunk == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64);
      invariant 22208u64 <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining;
      invariant (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64) <= bytes.len();
      invariant 22208u64 <= bytes.len() - (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining - 22208u64);
      invariant chunk == bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208);
      invariant 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208);
      invariant (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439;
      invariant defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208);
      invariant (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208 <= ((bytes.len() as u32) as i32);
      invariant chunk_len == 22208u64;
      invariant chunk == at(loop(1).entry, chunk);
      invariant bytes == old(bytes);
     invariant forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) };
      invariant bytes.len() == old(bytes.len());
      invariant bytes.len() <= 2147483647u64;
      invariant 0 <= ((bytes.len() as u32) as i32);
      invariant __rust_mir_27_size == 22208u64;
      invariant __rust_mir_33_live == 0;
      invariant __rust_mir_34_live == 0;
      invariant __rust_mir_36_live == 1;
      invariant (((__rust_mir_27_remaining as u32) as i32)) == at(loop(1).entry, (((__rust_mir_27_remaining as u32) as i32)));
      invariant __rust_mir_27_cursor == at(loop(1).entry, __rust_mir_27_cursor);
      invariant remainder_chunk == old(bytes) + old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32));
     invariant __rust_checked_93 == bytes.len() - bytes.len() % 4u64;
     invariant __rust_checked_94 == 22208u64;
      invariant remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
      invariant remainder_len == bytes.len() % 4u64;

      invariant chunk_len == 22208u64;
      invariant a <= 65520u32;
      invariant b <= 65520u32;
      invariant __rust_mir_36_size == 4u64;
      invariant 0 <= (((__rust_mir_36_remaining as u32) as i32)) and (((__rust_mir_36_remaining as u32) as i32)) <= 22208;
      invariant (((__rust_mir_36_remaining as u32) as i32)) % 4 == 0;
      invariant __rust_mir_36_cursor == at(loop(1).entry, chunk) + (22208 - (((__rust_mir_36_remaining as u32) as i32)));
      invariant to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))));
      invariant to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))));
      invariant to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))));
      invariant to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))));
      invariant to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))));
      invariant to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))));
      invariant to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))));
      invariant to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32))));
      invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))), to_integer(a));
      invariant 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))), to_integer(a), old(to_integer((self.b as u32))));
     preserve by {
       have 4 <= (((__rust_mir_36_remaining as u32) as i32)) by {
        have __rust_mir_36_remaining <= 2147483647u64 by arithmetic() using { __rust_mir_36_remaining <= 22208u64; };
        apply(adler_bounded_count_lower(__rust_mir_36_remaining, 4));
        assumption();
       }
       have 4u64 <= __rust_mir_36_remaining;
       have (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); __rust_mir_36_remaining <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining); };
       have (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) <= bytes.len() by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); __rust_mir_36_remaining <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining);(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= bytes.len(); };
       have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - __rust_mir_36_remaining) <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); __rust_mir_36_remaining <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining); };
       have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - __rust_mir_36_remaining) <= bytes.len() by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); __rust_mir_36_remaining <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining);((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - __rust_mir_36_remaining) <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining); (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) <= bytes.len(); };
       have 4u64 <= bytes.len() - ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - __rust_mir_36_remaining) by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); __rust_mir_36_remaining <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining);(((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) <= bytes.len(); 4u64 <= __rust_mir_36_remaining; };
       mark lane_head;
       have at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) % 4 == 0;
       have at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208;
       have 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32)));
       have 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32)));
       have 22208 <= 22208 by arithmetic() using { 22208 <= 22208; };
       have at(lane_head, __rust_mir_36_cursor) == at(loop(1).entry, chunk) + (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))));
       have 0 <= 22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) by arithmetic() using { 0 <= 22208; 22208 <= 22208; 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; };
       have (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) + 4 <= 22208 by arithmetic() using { 0 <= 22208; 22208 <= 22208; 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; };
       execute_until(assignment(__rust_mir_43, 0)); step();
       have __rust_mir_43 == at(lane_head, __rust_mir_36_cursor);
       execute_until(assignment(__rust_mir_43_len, 0)); step();
       have __rust_mir_43_len == 4u64;
       have __rust_mir_43 == at(loop(1).entry, chunk) + (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) by { rewrite(__rust_mir_43 == at(lane_head, __rust_mir_36_cursor)); assumption(); }
       have __rust_mir_43 == chunk + (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))));
       have (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4;
       have 22208 == 22208 by simp() using { chunk_len == 22208u64; };
       have 0 <= 22208 by assumption();
       have 22208 <= 22208 by assumption();
       have 22208 <= 22208 by simp() using { 22208 == 22208; 22208 <= 22208; };
       have (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) == 22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) by arithmetic() using {
         (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4;
         4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32)));
         at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208;
        };
       have 0 <= (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) by { rewrite((22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) == 22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))); assumption(); }
       have (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) + 4 <= 22208 by arithmetic() using { 22208 <= 22208; 0 <= 22208; 22208 <= 22208; (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; 0 <= 22208; 22208 <= 22208; 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; };
       have (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) <= (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) + 4 by arithmetic() using { 22208 == 22208; (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; 0 <= 22208; 22208 <= 22208; 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 0 <= (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4); (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) + 4 <= 22208; 0 <= 22208; 22208 <= 22208; };
       have __rust_mir_43 == chunk + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4);
       have 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208);
       have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439;
       have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208 <= ((bytes.len() as u32) as i32);
       have 0 <= ((bytes.len() as u32) as i32);
       have (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) <= 22204 by arithmetic() using { 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; };
       have 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) by arithmetic() using { 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439; 0 <= (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))); (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) <= 22204; (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208 <= ((bytes.len() as u32) as i32); 0 <= ((bytes.len() as u32) as i32); };
       apply(adler_absolute_chunk_access((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208), (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))), ((bytes.len() as u32) as i32))) using { 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439; 0 <= (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))); (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) <= 22204; (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208 <= ((bytes.len() as u32) as i32); 0 <= ((bytes.len() as u32) as i32); }
       execute_until(assignment(__rust_mir_45, 0));
       have (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4;
       mark vector_a;
       // Connect the actual constructor bytes to absolute input positions.
       // Prove machine equality before rewriting an Integer observation;
       // pointer rewriting inside an observation exposes different snapshots.
       have (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) <= 22204 by { rewrite((22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) == 22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))); arithmetic() using { 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; }; }
       apply(adler_absolute_chunk_pointer(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208), (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))) using { 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439; 0 <= (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4); (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) <= 22204; }
       have at(vector_a, __rust_mir_43) == (bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) by simp() using { __rust_mir_43 == chunk + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4); chunk == bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208); };
       have at(vector_a, __rust_mir_42.0[0]) == at(vector_a, (__rust_mir_43[0] as u32)) by normalize() using { __rust_mir_42.0[0] == at(vector_a, (__rust_mir_43[0] as u32)); };
       apply(adler_helper_byte_observation(at(vector_a, __rust_mir_43[0]))) using {};
       have to_integer(at(vector_a, __rust_mir_42.0[0])) == at(vector_a, to_integer((__rust_mir_43[0] as i32))) by {
        rewrite(at(vector_a, __rust_mir_42.0[0]) == at(vector_a, (__rust_mir_43[0] as u32)));
        normalize() using { at(vector_a, to_integer((__rust_mir_43[0] as u32))) == at(vector_a, to_integer((__rust_mir_43[0] as i32))); }
       }
       have at(vector_a, (__rust_mir_43[0] as i32)) == at(vector_a, (((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[0] as i32)) by {
        rewrite(at(vector_a, __rust_mir_43) == (bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4));
        simp();
       }
       apply(adler_absolute_chunk_byte_observation(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208), (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4), 0)) using { 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439; 0 <= (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4); (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) <= 22204; 0 <= 0; 0 <= 3; }
       have to_integer(at(vector_a, __rust_mir_42.0[0])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4)) + 0] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_42.0[0])) == at(vector_a, to_integer((__rust_mir_43[0] as i32))));
        rewrite(at(vector_a, (__rust_mir_43[0] as i32)) == at(vector_a, (((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[0] as i32)));
        normalize() using { at(vector_a, to_integer((((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[0] as i32))) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4)) + 0] as i32))); }
       }
       have at(vector_a, __rust_mir_42.0[1]) == at(vector_a, (__rust_mir_43[1] as u32)) by normalize() using { __rust_mir_42.0[1] == at(vector_a, (__rust_mir_43[1] as u32)); };
       apply(adler_helper_byte_observation(at(vector_a, __rust_mir_43[1]))) using {};
       have to_integer(at(vector_a, __rust_mir_42.0[1])) == at(vector_a, to_integer((__rust_mir_43[1] as i32))) by {
        rewrite(at(vector_a, __rust_mir_42.0[1]) == at(vector_a, (__rust_mir_43[1] as u32)));
        normalize() using { at(vector_a, to_integer((__rust_mir_43[1] as u32))) == at(vector_a, to_integer((__rust_mir_43[1] as i32))); }
       }
       have at(vector_a, (__rust_mir_43[1] as i32)) == at(vector_a, (((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[1] as i32)) by {
        rewrite(at(vector_a, __rust_mir_43) == (bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4));
        simp();
       }
       apply(adler_absolute_chunk_byte_observation(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208), (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4), 1)) using { 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439; 0 <= (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4); (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) <= 22204; 0 <= 1; 1 <= 3; }
       have to_integer(at(vector_a, __rust_mir_42.0[1])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4)) + 1] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_42.0[1])) == at(vector_a, to_integer((__rust_mir_43[1] as i32))));
        rewrite(at(vector_a, (__rust_mir_43[1] as i32)) == at(vector_a, (((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[1] as i32)));
        normalize() using { at(vector_a, to_integer((((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[1] as i32))) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4)) + 1] as i32))); }
       }
       have at(vector_a, __rust_mir_42.0[2]) == at(vector_a, (__rust_mir_43[2] as u32)) by normalize() using { __rust_mir_42.0[2] == at(vector_a, (__rust_mir_43[2] as u32)); };
       apply(adler_helper_byte_observation(at(vector_a, __rust_mir_43[2]))) using {};
       have to_integer(at(vector_a, __rust_mir_42.0[2])) == at(vector_a, to_integer((__rust_mir_43[2] as i32))) by {
        rewrite(at(vector_a, __rust_mir_42.0[2]) == at(vector_a, (__rust_mir_43[2] as u32)));
        normalize() using { at(vector_a, to_integer((__rust_mir_43[2] as u32))) == at(vector_a, to_integer((__rust_mir_43[2] as i32))); }
       }
       have at(vector_a, (__rust_mir_43[2] as i32)) == at(vector_a, (((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[2] as i32)) by {
        rewrite(at(vector_a, __rust_mir_43) == (bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4));
        simp();
       }
       apply(adler_absolute_chunk_byte_observation(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208), (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4), 2)) using { 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439; 0 <= (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4); (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) <= 22204; 0 <= 2; 2 <= 3; }
       have to_integer(at(vector_a, __rust_mir_42.0[2])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4)) + 2] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_42.0[2])) == at(vector_a, to_integer((__rust_mir_43[2] as i32))));
        rewrite(at(vector_a, (__rust_mir_43[2] as i32)) == at(vector_a, (((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[2] as i32)));
        normalize() using { at(vector_a, to_integer((((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[2] as i32))) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4)) + 2] as i32))); }
       }
       have at(vector_a, __rust_mir_42.0[3]) == at(vector_a, (__rust_mir_43[3] as u32)) by normalize() using { __rust_mir_42.0[3] == at(vector_a, (__rust_mir_43[3] as u32)); };
       apply(adler_helper_byte_observation(at(vector_a, __rust_mir_43[3]))) using {};
       have to_integer(at(vector_a, __rust_mir_42.0[3])) == at(vector_a, to_integer((__rust_mir_43[3] as i32))) by {
        rewrite(at(vector_a, __rust_mir_42.0[3]) == at(vector_a, (__rust_mir_43[3] as u32)));
        normalize() using { at(vector_a, to_integer((__rust_mir_43[3] as u32))) == at(vector_a, to_integer((__rust_mir_43[3] as i32))); }
       }
       have at(vector_a, (__rust_mir_43[3] as i32)) == at(vector_a, (((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[3] as i32)) by {
        rewrite(at(vector_a, __rust_mir_43) == (bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4));
        simp();
       }
       apply(adler_absolute_chunk_byte_observation(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208), (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4), 3)) using { 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439; 0 <= (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4); (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4) <= 22204; 0 <= 3; 3 <= 3; }
       have to_integer(at(vector_a, __rust_mir_42.0[3])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4)) + 3] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_42.0[3])) == at(vector_a, to_integer((__rust_mir_43[3] as i32))));
        rewrite(at(vector_a, (__rust_mir_43[3] as i32)) == at(vector_a, (((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[3] as i32)));
        normalize() using { at(vector_a, to_integer((((bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208)) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4))[3] as i32))) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + (22208 - (((__rust_mir_36_remaining as u32) as i32)) - 4)) + 3] as i32))); }
       }
       apply(uint32_to_integer_bounds(at(vector_a, a_vec.0[0])));
       apply(uint32_to_integer_bounds(at(vector_a, b_vec.0[0])));
       apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_42.0[0])));
       have 0 <= to_integer(at(vector_a, a_vec.0[0]));
       have 0 <= to_integer(at(vector_a, b_vec.0[0]));
       have to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))));
       have to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))));
       have 0 <= to_integer(at(vector_a, __rust_mir_42.0[0]));
       have to_integer(at(vector_a, __rust_mir_42.0[0])) <= 255;
       apply(adler_lane_iterator_add_contracts(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_42.0[0]))) using { 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[0])); to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[0])); to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[0])); to_integer(at(vector_a, __rust_mir_42.0[0])) <= 255; }
       apply(adler_lane_iterator_native_preservation(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_42.0[0]))) using { 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[0])); to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[0])); to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[0])); to_integer(at(vector_a, __rust_mir_42.0[0])) <= 255; }
       apply(uint32_to_integer_bounds(at(vector_a, a_vec.0[1])));
       apply(uint32_to_integer_bounds(at(vector_a, b_vec.0[1])));
       apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_42.0[1])));
       have 0 <= to_integer(at(vector_a, a_vec.0[1]));
       have 0 <= to_integer(at(vector_a, b_vec.0[1]));
       have to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))));
       have to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))));
       have 0 <= to_integer(at(vector_a, __rust_mir_42.0[1]));
       have to_integer(at(vector_a, __rust_mir_42.0[1])) <= 255;
       apply(adler_lane_iterator_add_contracts(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_42.0[1]))) using { 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[1])); to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[1])); to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[1])); to_integer(at(vector_a, __rust_mir_42.0[1])) <= 255; }
       apply(adler_lane_iterator_native_preservation(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_42.0[1]))) using { 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[1])); to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[1])); to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[1])); to_integer(at(vector_a, __rust_mir_42.0[1])) <= 255; }
       apply(uint32_to_integer_bounds(at(vector_a, a_vec.0[2])));
       apply(uint32_to_integer_bounds(at(vector_a, b_vec.0[2])));
       apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_42.0[2])));
       have 0 <= to_integer(at(vector_a, a_vec.0[2]));
       have 0 <= to_integer(at(vector_a, b_vec.0[2]));
       have to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))));
       have to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))));
       have 0 <= to_integer(at(vector_a, __rust_mir_42.0[2]));
       have to_integer(at(vector_a, __rust_mir_42.0[2])) <= 255;
       apply(adler_lane_iterator_add_contracts(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_42.0[2]))) using { 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[2])); to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[2])); to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[2])); to_integer(at(vector_a, __rust_mir_42.0[2])) <= 255; }
       apply(adler_lane_iterator_native_preservation(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_42.0[2]))) using { 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[2])); to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[2])); to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[2])); to_integer(at(vector_a, __rust_mir_42.0[2])) <= 255; }
       apply(uint32_to_integer_bounds(at(vector_a, a_vec.0[3])));
       apply(uint32_to_integer_bounds(at(vector_a, b_vec.0[3])));
       apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_42.0[3])));
       have 0 <= to_integer(at(vector_a, a_vec.0[3]));
       have 0 <= to_integer(at(vector_a, b_vec.0[3]));
       have to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))));
       have to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))));
       have 0 <= to_integer(at(vector_a, __rust_mir_42.0[3]));
       have to_integer(at(vector_a, __rust_mir_42.0[3])) <= 255;
       apply(adler_lane_iterator_add_contracts(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_42.0[3]))) using { 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[3])); to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[3])); to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[3])); to_integer(at(vector_a, __rust_mir_42.0[3])) <= 255; }
       apply(adler_lane_iterator_native_preservation(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_42.0[3]))) using { 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[3])); to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[3])); to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_42.0[3])); to_integer(at(vector_a, __rust_mir_42.0[3])) <= 255; }
       apply(adler_full_batch_prefix_window((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208), (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4))) using { 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) <= 2147461439; 0 <= (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4); (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) <= 22204; }
       apply(adler_signed_prefix_successors(((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)))) using { 0 <= ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)); ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) <= 2147483643; }
       have ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) == ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - at(lane_head, ((__rust_mir_36_remaining as u32) as i32)))) by { rewrite((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) == 22208 - at(lane_head, ((__rust_mir_36_remaining as u32) as i32))); normalize(); }
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a(at(vector_a, bytes), ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)), to_integer(a)) by { rewrite(((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) == ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - at(lane_head, ((__rust_mir_36_remaining as u32) as i32))))); simp(); }
       apply(uint32_to_integer_bounds(a)) using {};
       apply(uint32_less_equal_to_integer(a, 65520u32)) using { a <= 65520u32; }
       have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) by { have to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) == to_integer(22208 - at(lane_head, ((__rust_mir_36_remaining as u32) as i32))) by simp() using { (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) == 22208 - at(lane_head, ((__rust_mir_36_remaining as u32) as i32)); }; rewrite(to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) == to_integer(22208 - at(lane_head, ((__rust_mir_36_remaining as u32) as i32)))); simp(); }
       apply(uint32_add_to_integer(at(vector_a, a_vec.0[0]), at(vector_a, __rust_mir_42.0[0]))) using { to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295; }
       have to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))); assumption(); }
       apply(uint32_add_to_integer(at(vector_a, a_vec.0[1]), at(vector_a, __rust_mir_42.0[1]))) using { to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295; }
       have to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))); assumption(); }
       apply(uint32_add_to_integer(at(vector_a, a_vec.0[2]), at(vector_a, __rust_mir_42.0[2]))) using { to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295; }
       have to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))); assumption(); }
       apply(uint32_add_to_integer(at(vector_a, a_vec.0[3]), at(vector_a, __rust_mir_42.0[3]))) using { to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295; }
       have to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))); assumption(); }
       apply(adler_native_deferred_b_step((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_42.0[0]), at(vector_a, __rust_mir_42.0[1]), at(vector_a, __rust_mir_42.0[2]), at(vector_a, __rust_mir_42.0[3]))) using { 0 <= (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4); (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) <= 22204; 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295; to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3]))) <= 4294967295; }
       apply(adler_nonnegative_deferred_b_step((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_42.0[0]), at(vector_a, __rust_mir_42.0[1]), at(vector_a, __rust_mir_42.0[2]), at(vector_a, __rust_mir_42.0[3]))) using { 0 <= (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4); (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) <= 22204; 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295; to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3]))) <= 4294967295; }
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b(at(vector_a, bytes), ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)), to_integer(at(vector_a, a)), old(to_integer((self.b as u32)))) by { have to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) == to_integer(22208 - at(lane_head, ((__rust_mir_36_remaining as u32) as i32))) by simp() using { (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) == 22208 - at(lane_head, ((__rust_mir_36_remaining as u32) as i32)); }; rewrite(((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) == ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - at(lane_head, ((__rust_mir_36_remaining as u32) as i32))))); rewrite(to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) == to_integer(22208 - at(lane_head, ((__rust_mir_36_remaining as u32) as i32)))); simp(); }
       apply(adler_native_deferred_b_prefix_step(at(vector_a, bytes), ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)), (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4), to_integer(a), old(to_integer((self.b as u32))), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_42.0[0]), at(vector_a, __rust_mir_42.0[1]), at(vector_a, __rust_mir_42.0[2]), at(vector_a, __rust_mir_42.0[3]))) using {
        0 <= ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)); ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) <= 2147483643;
        0 <= to_integer(a); to_integer(a) <= 65520;
        truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a(at(vector_a, bytes), ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)), to_integer(a));
        to_integer(at(vector_a, __rust_mir_42.0[0])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4))] as i32)));
        to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_42.0[1])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) + 1] as i32)));
        to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_42.0[2])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) + 2] as i32)));
        to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_42.0[3])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) + 3] as i32)));
        to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295;
        0 <= (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4); (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) <= 22204; 0 <= old(to_integer((self.b as u32))); 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b(at(vector_a, bytes), ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)), to_integer(at(vector_a, a)), old(to_integer((self.b as u32)))); to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3]))) <= 4294967295;
       }
       apply(adler_native_four_lane_a_prefix_step(at(vector_a, bytes), ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)), to_integer(a), to_integer(a), at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, __rust_mir_42.0[0]), at(vector_a, __rust_mir_42.0[1]), at(vector_a, __rust_mir_42.0[2]), at(vector_a, __rust_mir_42.0[3]))) using {
        0 <= ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)); ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) <= 2147483643;
        0 <= to_integer(a); to_integer(a) <= 65520;
        truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a(at(vector_a, bytes), ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)), to_integer(a));
        to_integer(at(vector_a, __rust_mir_42.0[0])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4))] as i32)));
        to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_42.0[0])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_42.0[1])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) + 1] as i32)));
        to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_42.0[1])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_42.0[2])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) + 2] as i32)));
        to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_42.0[2])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_42.0[3])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) + 3] as i32)));
        to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_42.0[3])) <= 4294967295;
       }
       execute_until(assignment(__rust_mir_48, 0));
       have a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]);
       have b_vec.0[0] == at(vector_a, b_vec.0[0]);
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]); };
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])) by simp() using { a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]); };
       have to_integer(b_vec.0[0]) + to_integer(a_vec.0[0]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])); to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])); to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])) <= 4294967295; };
       have a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]);
       have b_vec.0[1] == at(vector_a, b_vec.0[1]);
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]); };
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]); };
       have to_integer(b_vec.0[1]) + to_integer(a_vec.0[1]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) <= 4294967295; };
       have a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]);
       have b_vec.0[2] == at(vector_a, b_vec.0[2]);
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]); };
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]); };
       have to_integer(b_vec.0[2]) + to_integer(a_vec.0[2]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) <= 4294967295; };
       have a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]);
       have b_vec.0[3] == at(vector_a, b_vec.0[3]);
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]); };
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]); };
       have to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) <= 4294967295; };
       mark vector_b;
       execute_until(back_edge());
       have a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]);
       have b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]));
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])) by simp() using { a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; };
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); };
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; };
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); };
       have a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]);
       have b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]));
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; };
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); };
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; };
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); };
       have a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]);
       have b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]));
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; };
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); };
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; };
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); };
       have a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]);
       have b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]));
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; };
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); };
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; };
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4)); };
       have 0 <= (((__rust_mir_36_remaining as u32) as i32)) by arithmetic() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); };
       have (((__rust_mir_36_remaining as u32) as i32)) <= 22208 by arithmetic() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; };
       have 0 <= (((__rust_mir_36_remaining as u32) as i32)) and (((__rust_mir_36_remaining as u32) as i32)) <= 22208 by assumption();
       have (((__rust_mir_36_remaining as u32) as i32)) % 4 == 0 by { rewrite((((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4); normalize() using { at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) % 4 == 0; 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; } }
       have __rust_mir_36_cursor == at(lane_head, __rust_mir_36_cursor) + 4;
       have (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) + 4 == 22208 - (((__rust_mir_36_remaining as u32) as i32)) by arithmetic() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; };
       have 0 <= 22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) by arithmetic() using { 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; };
       have 22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22204 by arithmetic() using { 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; };
       have 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) by arithmetic() using { 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); };
       have defined(22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) by apply(int32_nonnegative_subtract_within_value_is_defined(22208, at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))) using { 0 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; };
       have (at(loop(1).entry, chunk) + (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))) + 4 == at(loop(1).entry, chunk) + ((22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) + 4) by apply(adler_bounded_pointer_association(at(loop(1).entry, chunk), 22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))) using { defined(22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))); 0 <= 22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); 22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22204; };
       have __rust_mir_36_cursor == at(loop(1).entry, chunk) + (22208 - (((__rust_mir_36_remaining as u32) as i32))) by { rewrite(__rust_mir_36_cursor == at(lane_head, __rust_mir_36_cursor) + 4); rewrite(at(lane_head, __rust_mir_36_cursor) == at(loop(1).entry, chunk) + (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))); rewrite((at(loop(1).entry, chunk) + (22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32))))) + 4 == at(loop(1).entry, chunk) + ((22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) + 4)); rewrite((22208 - at(lane_head, (((__rust_mir_36_remaining as u32) as i32)))) + 4 == 22208 - (((__rust_mir_36_remaining as u32) as i32))); normalize() using {}; }
       have (((__rust_mir_36_remaining as u32) as i32)) < at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) by arithmetic() using { (((__rust_mir_36_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_36_remaining as u32) as i32))); at(lane_head, (((__rust_mir_36_remaining as u32) as i32))) <= 22208; 22208 <= 22208; };
       have chunk == bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) by assumption();
       have 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) by assumption();
       have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) <= 2147461439 by assumption();
       have defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208) by assumption();
       have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - (((__rust_mir_27_remaining as u32) as i32)) - 22208) + 22208 <= ((bytes.len() as u32) as i32) by assumption();
       have chunk_len == 22208u64 by assumption();
       have chunk == at(loop(1).entry, chunk) by assumption();
       have bytes == old(bytes) by assumption();
       have bytes.len() == old(bytes.len()) by assumption();
       have bytes.len() <= 2147483647u64 by assumption();
       have 0 <= ((bytes.len() as u32) as i32) by assumption();
       have __rust_mir_27_size == 22208u64 by assumption();
       have __rust_mir_33_live == 0 by assumption();
       have __rust_mir_34_live == 0 by assumption();
       have __rust_mir_36_live == 1 by assumption();
       have (((__rust_mir_27_remaining as u32) as i32)) == at(loop(1).entry, (((__rust_mir_27_remaining as u32) as i32))) by assumption();
       have __rust_mir_27_cursor == at(loop(1).entry, __rust_mir_27_cursor) by assumption();
       have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64 by assumption();
       have remainder_len == bytes.len() % 4u64 by assumption();
       have chunk_len == 22208u64 by assumption();
       have a <= 65520u32 by assumption();
       have b <= 65520u32 by assumption();
       have __rust_mir_36_size == 4u64 by assumption();
       have 0 <= (((__rust_mir_36_remaining as u32) as i32)) and (((__rust_mir_36_remaining as u32) as i32)) <= 22208 by assumption();
       have (((__rust_mir_36_remaining as u32) as i32)) % 4 == 0 by assumption();
       have __rust_mir_36_cursor == at(loop(1).entry, chunk) + (22208 - (((__rust_mir_36_remaining as u32) as i32))) by assumption();
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by assumption();
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by assumption();
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by assumption();
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by assumption();
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by assumption();
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by assumption();
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by assumption();
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(22208, (((__rust_mir_36_remaining as u32) as i32)))) by assumption();
       have __rust_mir_36_remaining == at(lane_head, __rust_mir_36_remaining) - 4u64;
       have 4u64 <= at(lane_head, __rust_mir_36_remaining);
       have at(lane_head, __rust_mir_36_remaining) <= 22208u64;
       have __rust_mir_36_remaining <= 22208u64 by arithmetic() using {
        __rust_mir_36_remaining == at(lane_head, __rust_mir_36_remaining) - 4u64;
        4u64 <= at(lane_head, __rust_mir_36_remaining);
        at(lane_head, __rust_mir_36_remaining) <= 22208u64;
       };
       have __rust_mir_36_remaining < at(lane_head, __rust_mir_36_remaining) by arithmetic() using {
        __rust_mir_36_remaining == at(lane_head, __rust_mir_36_remaining) - 4u64;
        4u64 <= at(lane_head, __rust_mir_36_remaining);
        at(lane_head, __rust_mir_36_remaining) <= 22208u64;
       };
       have __rust_mir_36_remaining == at(lane_head, __rust_mir_36_remaining) - 4u64;
       have 4u64 <= at(lane_head, __rust_mir_36_remaining) by assumption();
       have __rust_mir_36_remaining <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) by arithmetic() using { __rust_mir_36_remaining == at(lane_head, __rust_mir_36_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_36_remaining); at(lane_head, __rust_mir_36_remaining) <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining); bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); };
       have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - at(lane_head, __rust_mir_36_remaining)) <= 18446744073709551611u64 by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); at(lane_head, __rust_mir_36_remaining) <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining); 4u64 <= at(lane_head, __rust_mir_36_remaining); };
       have at(lane_head, __rust_mir_36_cursor) + 4 == bytes + (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - at(lane_head, __rust_mir_36_remaining)) + 4u64) by arithmetic() using { at(lane_head, __rust_mir_36_cursor) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - at(lane_head, __rust_mir_36_remaining)); ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - at(lane_head, __rust_mir_36_remaining)) <= 18446744073709551611u64; };
       have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - __rust_mir_36_remaining) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - at(lane_head, __rust_mir_36_remaining)) + 4u64 by arithmetic() using { __rust_mir_36_remaining == at(lane_head, __rust_mir_36_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_36_remaining); at(lane_head, __rust_mir_36_remaining) <= (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining); bytes.len() % 4u64 <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= bytes.len() - bytes.len() % 4u64; __rust_mir_27_remaining <= ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); };
       have __rust_mir_36_cursor == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - __rust_mir_36_remaining) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - __rust_mir_36_remaining) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) - at(lane_head, __rust_mir_36_remaining)) + 4u64); simp(); }
       apply(adler_full_batch_end_guard((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208), ((__rust_mir_36_remaining as u32) as i32))) using { 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) <= 2147461439; 0 <= ((__rust_mir_36_remaining as u32) as i32); ((__rust_mir_36_remaining as u32) as i32) <= 22208; }
       have defined(((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32)))) by { both { assumption(); } and { both { assumption(); } and { assumption(); } } }
       // Retain the exact A transition at the actual inner back edge.
       have ((__rust_mir_36_remaining as u32) as i32) <= 22204 by arithmetic() using { ((__rust_mir_36_remaining as u32) as i32) == at(lane_head, ((__rust_mir_36_remaining as u32) as i32)) - 4; 4 <= at(lane_head, ((__rust_mir_36_remaining as u32) as i32)); at(lane_head, ((__rust_mir_36_remaining as u32) as i32)) <= 22208; };
       apply(adler_full_batch_within_advance(((__rust_mir_36_remaining as u32) as i32))) using { 0 <= ((__rust_mir_36_remaining as u32) as i32); ((__rust_mir_36_remaining as u32) as i32) <= 22204; }
       apply(adler_full_batch_prefix_advance((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208), (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4))) using { 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) <= 2147461439; 0 <= (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4); (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) <= 22204; }
       have ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))) == ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) + 4 by {
        rewrite(((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) + 4 == (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + ((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) + 4));
        rewrite((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) + 4 == 22208 - ((__rust_mir_36_remaining as u32) as i32));
        normalize();
       }
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))), to_integer(a)) by {
        rewrite(((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))) == ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) + 4);
        rewrite(a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]));
        rewrite(a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]));
        rewrite(a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]));
        rewrite(a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]));
        simp();
       }
       have (22208 - ((__rust_mir_36_remaining as u32) as i32)) == (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) + 4 by { rewrite((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) + 4 == 22208 - ((__rust_mir_36_remaining as u32) as i32)); normalize(); }
       have 0 <= adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by {
        have to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) == to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) + 4) by simp() using { (22208 - ((__rust_mir_36_remaining as u32) as i32)) == (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) + 4; };
        rewrite(to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) == to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) + 4));
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]); };
        rewrite(to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])));
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]); };
        rewrite(to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])));
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]); };
        rewrite(to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])));
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])); };
        rewrite(to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))));
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); };
        rewrite(to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))));
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); };
        rewrite(to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))));
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); };
        rewrite(to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))));
        simp();
       }
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))), to_integer(a), old(to_integer((self.b as u32)))) by {
        rewrite(((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))) == ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4)) + 4);
        have to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) == to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) + 4) by simp() using { (22208 - ((__rust_mir_36_remaining as u32) as i32)) == (22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) + 4; };
        rewrite(to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32))) == to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32) - 4) + 4));
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]); };
        rewrite(to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])));
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]); };
        rewrite(to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])));
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]); };
        rewrite(to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])));
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0])); };
        rewrite(to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_42.0[0]))));
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1])); };
        rewrite(to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_42.0[1]))));
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2])); };
        rewrite(to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_42.0[2]))));
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3])); };
        rewrite(to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_42.0[3]))));
        simp();
       }
       close_invariants();
      }
     }
     have __rust_mir_36_remaining < 4u64 by { cases {
      not (0u64 < __rust_mir_36_remaining) => { have __rust_mir_36_remaining <= 0u64; arithmetic() using { __rust_mir_36_remaining <= 0u64; } }
      not (4u64 <= __rust_mir_36_remaining) => { simp(); }
     } }
     have __rust_mir_36_remaining <= 2147483647u64 by arithmetic() using { __rust_mir_36_remaining <= 22208u64; };
     apply(adler_bounded_count(__rust_mir_36_remaining));
     apply(uint64_less_than_to_integer(__rust_mir_36_remaining, 4u64)) using { __rust_mir_36_remaining < 4u64; }
     have to_integer((((__rust_mir_36_remaining as u32) as i32))) < to_integer(4) by arithmetic() using {
      to_integer((((__rust_mir_36_remaining as u32) as i32))) == to_integer(__rust_mir_36_remaining);
      to_integer(__rust_mir_36_remaining) < to_integer(4u64);
     };
     have to_integer((((__rust_mir_36_remaining as u32) as i32))) <= to_integer(3) by arithmetic() using { to_integer((((__rust_mir_36_remaining as u32) as i32))) < to_integer(4); };
     apply(int32_to_integer_less_equal_implies_less_equal((((__rust_mir_36_remaining as u32) as i32)), 3));
     have (((__rust_mir_36_remaining as u32) as i32)) < 4 by arithmetic() using { (((__rust_mir_36_remaining as u32) as i32)) <= 3; };
     have (((__rust_mir_36_remaining as u32) as i32)) % 4 == (((__rust_mir_36_remaining as u32) as i32)) by normalize() using { 0 <= (((__rust_mir_36_remaining as u32) as i32)); (((__rust_mir_36_remaining as u32) as i32)) < 4; };
     have (((__rust_mir_36_remaining as u32) as i32)) == 0 by simp() using { (((__rust_mir_36_remaining as u32) as i32)) % 4 == 0; (((__rust_mir_36_remaining as u32) as i32)) % 4 == (((__rust_mir_36_remaining as u32) as i32)); };
     have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + 22208 == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) by simp();
     have ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32))) == (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)) by {
      rewrite(((__rust_mir_36_remaining as u32) as i32) == 0);
      have 22208 - 0 == 22208 by normalize();
      rewrite(22208 - 0 == 22208);
      assumption();
     }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(a)) by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)) == ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32)))); simp(); }
     apply(adler_complete_full_batch_position(((__rust_mir_36_remaining as u32) as i32))) using { ((__rust_mir_36_remaining as u32) as i32) == 0; }
     have 0 <= adler_lane_b(to_integer(b) + 22208 * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(22208 == to_integer(22208 - ((__rust_mir_36_remaining as u32) as i32))); assumption(); }
     have truncating_remainder(adler_lane_b(to_integer(b) + 22208 * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(22208 == to_integer((22208 - ((__rust_mir_36_remaining as u32) as i32)))); rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)) == ((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) - 22208) + (22208 - ((__rust_mir_36_remaining as u32) as i32)))); simp(); }
     mark full_lane_prefix;
     have truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521) == adler_spec_a(at(full_lane_prefix, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(at(full_lane_prefix, a))) by simp();
     apply(uint32_to_integer_bounds(at(full_lane_prefix, a))) using {};
     apply(uint32_to_integer_bounds(at(full_lane_prefix, a_vec.0[0]))) using {};
     apply(uint32_to_integer_bounds(at(full_lane_prefix, a_vec.0[1]))) using {};
     apply(uint32_to_integer_bounds(at(full_lane_prefix, a_vec.0[2]))) using {};
     apply(uint32_to_integer_bounds(at(full_lane_prefix, a_vec.0[3]))) using {};
     apply(adler_lane_a_reduction(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])))) using { 0 <= to_integer(at(full_lane_prefix, a)); 0 <= to_integer(at(full_lane_prefix, a_vec.0[0])); 0 <= to_integer(at(full_lane_prefix, a_vec.0[1])); 0 <= to_integer(at(full_lane_prefix, a_vec.0[2])); 0 <= to_integer(at(full_lane_prefix, a_vec.0[3])); }
     have truncating_remainder(adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))), 65521) == adler_spec_b(at(full_lane_prefix, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(at(full_lane_prefix, a)), old(to_integer((self.b as u32)))) by simp();
     // The deferred scalar seed and all lane observations are still exact.
     apply(uint32_to_integer_bounds(at(full_lane_prefix, b))) using {};
     apply(uint32_to_integer_bounds(at(full_lane_prefix, b_vec.0[0]))) using {};
     apply(uint32_to_integer_bounds(at(full_lane_prefix, b_vec.0[1]))) using {};
     apply(uint32_to_integer_bounds(at(full_lane_prefix, b_vec.0[2]))) using {};
     apply(uint32_to_integer_bounds(at(full_lane_prefix, b_vec.0[3]))) using {};
     have 0 <= to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by arithmetic() using { 0 <= to_integer(at(full_lane_prefix, b)); 0 <= to_integer(at(full_lane_prefix, a)); };
     have 0 <= adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))) by simp();
     apply(adler_lane_b_reduction(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3])))) using { 0 <= to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)); 0 <= to_integer(at(full_lane_prefix, a_vec.0[1])); 0 <= to_integer(at(full_lane_prefix, a_vec.0[2])); 0 <= to_integer(at(full_lane_prefix, a_vec.0[3])); 0 <= to_integer(at(full_lane_prefix, b_vec.0[0])); 0 <= to_integer(at(full_lane_prefix, b_vec.0[1])); 0 <= to_integer(at(full_lane_prefix, b_vec.0[2])); 0 <= to_integer(at(full_lane_prefix, b_vec.0[3])); 0 <= adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))); }
     execute_until(assignment(__rust_mir_52, 0)); step();
     have __rust_mir_51 == 22208u32;
     have __rust_mir_52 <= 65520u32 by simp() using { a <= 65520u32; };
     apply(uint32_less_equal_to_integer(__rust_mir_52, 65520u32)) using { __rust_mir_52 <= 65520u32; }
     have to_integer(__rust_mir_51) * to_integer(__rust_mir_52) <= 1455068160 by {
      rewrite(__rust_mir_51 == 22208u32);
      arithmetic() using { to_integer(__rust_mir_52) <= 65520; }
     }
     have to_integer(__rust_mir_51) * to_integer(__rust_mir_52) <= 4294967295 by arithmetic() using { to_integer(__rust_mir_51) * to_integer(__rust_mir_52) <= 1455068160; };
     apply(uint32_multiply_guard_by_integer_bound(__rust_mir_51, __rust_mir_52)) using { to_integer(__rust_mir_51) * to_integer(__rust_mir_52) <= 4294967295; }
     apply(uint32_multiply_to_integer(__rust_mir_51, __rust_mir_52)) using { __rust_mir_52 == 0u32 or __rust_mir_51 <= 4294967295u32 / __rust_mir_52; }
     mark full_product;
     have to_integer(at(full_product, __rust_mir_51)) * to_integer(at(full_product, __rust_mir_52)) <= 1455068160 by simp() using { to_integer(__rust_mir_51) * to_integer(__rust_mir_52) <= 1455068160; };
     have at(full_product, __rust_mir_52) == 0u32 or at(full_product, __rust_mir_51) <= 4294967295u32 / at(full_product, __rust_mir_52) by simp() using { __rust_mir_52 == 0u32 or __rust_mir_51 <= 4294967295u32 / __rust_mir_52; };
     apply(uint32_multiply_to_integer(at(full_product, __rust_mir_51), at(full_product, __rust_mir_52))) using { at(full_product, __rust_mir_52) == 0u32 or at(full_product, __rust_mir_51) <= 4294967295u32 / at(full_product, __rust_mir_52); }
     if __rust_mir_52 == 0u32 {
      execute_until(assignment(__rust_mir_50, 0)); step();
     } else {
      have __rust_mir_51 <= 4294967295u32 / __rust_mir_52 by { cases {
       __rust_mir_52 == 0u32 => { contradiction(not (__rust_mir_52 == 0u32)); }
       __rust_mir_51 <= 4294967295u32 / __rust_mir_52 => { assumption(); }
      } }
      execute_until(assignment(__rust_mir_50, 0)); step();
     }
     have __rust_mir_50 == at(full_product, __rust_mir_51) * at(full_product, __rust_mir_52);
     have to_integer(__rust_mir_50) <= 1455068160 by {
      rewrite(__rust_mir_50 == at(full_product, __rust_mir_51) * at(full_product, __rust_mir_52));
      rewrite(to_integer(at(full_product, __rust_mir_51) * at(full_product, __rust_mir_52)) == to_integer(at(full_product, __rust_mir_51)) * to_integer(at(full_product, __rust_mir_52)));
      assumption();
     }
     apply(uint32_less_equal_to_integer(b, 65520u32)) using { b <= 65520u32; }
     have to_integer(b) + to_integer(__rust_mir_50) <= 4294967295 by arithmetic() using { to_integer(b) <= 65520; to_integer(__rust_mir_50) <= 1455068160; };
     apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_50)) using { to_integer(b) + to_integer(__rust_mir_50) <= 4294967295; }
     apply(uint32_add_to_integer(b, __rust_mir_50)) using { to_integer(b) + to_integer(__rust_mir_50) <= 4294967295; }
     have at(full_product, __rust_mir_51) == 22208u32 by simp();
     have at(full_product, __rust_mir_52) == at(full_lane_prefix, a) by simp();
     have to_integer(__rust_mir_50) == 22208 * to_integer(at(full_lane_prefix, a)) by {
      rewrite(__rust_mir_50 == at(full_product, __rust_mir_51) * at(full_product, __rust_mir_52));
      rewrite(to_integer(at(full_product, __rust_mir_51) * at(full_product, __rust_mir_52)) == to_integer(at(full_product, __rust_mir_51)) * to_integer(at(full_product, __rust_mir_52)));
      rewrite(at(full_product, __rust_mir_51) == 22208u32);
      rewrite(at(full_product, __rust_mir_52) == at(full_lane_prefix, a));
      normalize();
     }
     mark full_seed_add;
     have at(full_seed_add, b) == at(full_lane_prefix, b) by simp();
     have to_integer(at(full_seed_add, __rust_mir_50)) == 22208 * to_integer(at(full_lane_prefix, a)) by simp();
     have to_integer(at(full_seed_add, b) + at(full_seed_add, __rust_mir_50)) == to_integer(at(full_seed_add, b)) + to_integer(at(full_seed_add, __rust_mir_50)) by simp();
     execute_until(assignment(__rust_mir_56, 0)); step();
     mark full_reduction_a;
     have at(full_reduction_a, a_vec.0[0]) == at(full_lane_prefix, a_vec.0[0]) by simp();
     have at(full_reduction_a, a_vec.0[1]) == at(full_lane_prefix, a_vec.0[1]) by simp();
     have at(full_reduction_a, a_vec.0[2]) == at(full_lane_prefix, a_vec.0[2]) by simp();
     have at(full_reduction_a, a_vec.0[3]) == at(full_lane_prefix, a_vec.0[3]) by simp();
     have b == at(full_seed_add, b) + at(full_seed_add, __rust_mir_50) by simp();
     have to_integer(b) == to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by {
      rewrite(b == at(full_seed_add, b) + at(full_seed_add, __rust_mir_50));
      rewrite(to_integer(at(full_seed_add, b) + at(full_seed_add, __rust_mir_50)) == to_integer(at(full_seed_add, b)) + to_integer(at(full_seed_add, __rust_mir_50)));
      rewrite(at(full_seed_add, b) == at(full_lane_prefix, b));
      rewrite(to_integer(at(full_seed_add, __rust_mir_50)) == 22208 * to_integer(at(full_lane_prefix, a)));
      normalize();
     }
     execute_until(assignment(__rust_mir_58, 0)); step();
     mark full_reduction_b;
     have at(full_reduction_b, b_vec.0[0]) == at(full_lane_prefix, b_vec.0[0]) by simp();
     have at(full_reduction_b, b_vec.0[1]) == at(full_lane_prefix, b_vec.0[1]) by simp();
     have at(full_reduction_b, b_vec.0[2]) == at(full_lane_prefix, b_vec.0[2]) by simp();
     have at(full_reduction_b, b_vec.0[3]) == at(full_lane_prefix, b_vec.0[3]) by simp();
     have to_integer(at(full_reduction_b, b)) == to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by simp();
     execute_until(assignment(b, 2));
     mark full_scalar_mod;
     have to_integer(a) == to_integer(at(full_lane_prefix, a));
     have __rust_checked_11 == 65521u32;
     have to_integer(__rust_checked_11) == 65521 by { rewrite(__rust_checked_11 == 65521u32); normalize(); }
     have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[0])), to_integer(__rust_checked_11)) by simp();
     have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[0])), 65521) by {
      rewrite(at(full_lane_prefix, a_vec.0[0]) == at(full_reduction_a, a_vec.0[0]));
      rewrite(65521 == to_integer(__rust_checked_11));
      assumption();
     }
     have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[1])), to_integer(__rust_checked_11)) by simp();
     have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521) by {
      rewrite(at(full_lane_prefix, a_vec.0[1]) == at(full_reduction_a, a_vec.0[1]));
      rewrite(65521 == to_integer(__rust_checked_11));
      assumption();
     }
     have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[2])), to_integer(__rust_checked_11)) by simp();
     have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521) by {
      rewrite(at(full_lane_prefix, a_vec.0[2]) == at(full_reduction_a, a_vec.0[2]));
      rewrite(65521 == to_integer(__rust_checked_11));
      assumption();
     }
     have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(full_reduction_a, a_vec.0[3])), to_integer(__rust_checked_11)) by simp();
     have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521) by {
      rewrite(at(full_lane_prefix, a_vec.0[3]) == at(full_reduction_a, a_vec.0[3]));
      rewrite(65521 == to_integer(__rust_checked_11));
      assumption();
     }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521) by {
      rewrite(to_integer(a) == to_integer(at(full_lane_prefix, a)));
      rewrite(to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[0])), 65521));
      rewrite(to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521));
      rewrite(to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521));
      rewrite(to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521));
      rewrite(truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521) == truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[0])), 65521), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521)), 65521));
      normalize();
     }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(a)) by {
      rewrite(truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == truncating_remainder(adler_lane_a(to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[0])), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3]))), 65521));
      rewrite(to_integer(a) == to_integer(at(full_lane_prefix, a)));
      simp();
     }
     have to_integer(at(full_scalar_mod, b)) == to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)) by simp();
     have __rust_checked_8 == 65521u32;
     have to_integer(__rust_checked_8) == 65521 by { rewrite(__rust_checked_8 == 65521u32); normalize(); }
     have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[0])), to_integer(__rust_checked_8)) by simp();
     have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[0])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[0]) == at(full_reduction_b, b_vec.0[0])); rewrite(65521 == to_integer(__rust_checked_8)); assumption(); }
     have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[1])), to_integer(__rust_checked_8)) by simp();
     have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[1])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[1]) == at(full_reduction_b, b_vec.0[1])); rewrite(65521 == to_integer(__rust_checked_8)); assumption(); }
     have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[2])), to_integer(__rust_checked_8)) by simp();
     have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[2])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[2]) == at(full_reduction_b, b_vec.0[2])); rewrite(65521 == to_integer(__rust_checked_8)); assumption(); }
     have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(full_reduction_b, b_vec.0[3])), to_integer(__rust_checked_8)) by simp();
     have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[3])), 65521) by { rewrite(at(full_lane_prefix, b_vec.0[3]) == at(full_reduction_b, b_vec.0[3])); rewrite(65521 == to_integer(__rust_checked_8)); assumption(); }
     step();
     have b == at(full_scalar_mod, b) % 65521u32;
     apply(uint32_remainder_to_integer(at(full_scalar_mod, b), 65521u32)) using { 65521u32 != 0u32; }
     have to_integer(b) == truncating_remainder(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), 65521) by { rewrite(b == at(full_scalar_mod, b) % 65521u32); rewrite(to_integer(at(full_scalar_mod, b) % 65521u32) == truncating_remainder(to_integer(at(full_scalar_mod, b)), to_integer(65521u32))); rewrite(to_integer(at(full_scalar_mod, b)) == to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a))); normalize(); }
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == truncating_remainder(adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))), 65521) by {
      rewrite(to_integer(b) == truncating_remainder(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), 65521));
      rewrite(to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[1])), 65521));
      rewrite(to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[2])), 65521));
      rewrite(to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(full_lane_prefix, a_vec.0[3])), 65521));
      rewrite(to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[0])), 65521));
      rewrite(to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[1])), 65521));
      rewrite(to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[2])), 65521));
      rewrite(to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(full_lane_prefix, b_vec.0[3])), 65521));
      simp();
     }
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == truncating_remainder(adler_lane_b(to_integer(at(full_lane_prefix, b)) + 22208 * to_integer(at(full_lane_prefix, a)), to_integer(at(full_lane_prefix, a_vec.0[1])), to_integer(at(full_lane_prefix, a_vec.0[2])), to_integer(at(full_lane_prefix, a_vec.0[3])), to_integer(at(full_lane_prefix, b_vec.0[0])), to_integer(at(full_lane_prefix, b_vec.0[1])), to_integer(at(full_lane_prefix, b_vec.0[2])), to_integer(at(full_lane_prefix, b_vec.0[3]))), 65521)); simp(); }
     apply(uint32_remainder_less_than_divisor(at(full_scalar_mod, b), 65521u32)) using { 65521u32 != 0u32; }
     have b < 65521u32 by { rewrite(b == at(full_scalar_mod, b) % 65521u32); assumption(); }
     apply(uint32_less_than_to_integer(b, 65521u32)) using { b < 65521u32; }
     have to_integer(b) <= 65520 by arithmetic() using { to_integer(b) < 65521; };
     apply(uint32_to_integer_less_equal_implies_less_equal(b, 65520u32)) using { to_integer(b) <= 65520; }
     have __rust_checked_9 == 65521u32;
     have 65521u32 == __rust_checked_9 by simp() using { __rust_checked_9 == 65521u32; };
     have __rust_checked_12 == 65521u32;
     have 65521u32 == __rust_checked_12 by simp() using { __rust_checked_12 == 65521u32; };
     have a_vec.0[0] < __rust_checked_12;
     have a_vec.0[0] < 65521u32 by { rewrite(65521u32 == __rust_checked_12); assumption(); }
     apply(uint32_less_than_to_integer(a_vec.0[0], 65521u32)) using { a_vec.0[0] < 65521u32; }
     have to_integer(a_vec.0[0]) <= 65520 by arithmetic() using { to_integer(a_vec.0[0]) < 65521; };
     have a_vec.0[1] < __rust_checked_12;
     have a_vec.0[1] < 65521u32 by { rewrite(65521u32 == __rust_checked_12); assumption(); }
     apply(uint32_less_than_to_integer(a_vec.0[1], 65521u32)) using { a_vec.0[1] < 65521u32; }
     have to_integer(a_vec.0[1]) <= 65520 by arithmetic() using { to_integer(a_vec.0[1]) < 65521; };
     have a_vec.0[2] < __rust_checked_12;
     have a_vec.0[2] < 65521u32 by { rewrite(65521u32 == __rust_checked_12); assumption(); }
     apply(uint32_less_than_to_integer(a_vec.0[2], 65521u32)) using { a_vec.0[2] < 65521u32; }
     have to_integer(a_vec.0[2]) <= 65520 by arithmetic() using { to_integer(a_vec.0[2]) < 65521; };
     have a_vec.0[3] < __rust_checked_12;
     have a_vec.0[3] < 65521u32 by { rewrite(65521u32 == __rust_checked_12); assumption(); }
     apply(uint32_less_than_to_integer(a_vec.0[3], 65521u32)) using { a_vec.0[3] < 65521u32; }
     have to_integer(a_vec.0[3]) <= 65520 by arithmetic() using { to_integer(a_vec.0[3]) < 65521; };
     have b_vec.0[0] < __rust_checked_9;
     have b_vec.0[0] < 65521u32 by { rewrite(65521u32 == __rust_checked_9); assumption(); }
     apply(uint32_less_than_to_integer(b_vec.0[0], 65521u32)) using { b_vec.0[0] < 65521u32; }
     have to_integer(b_vec.0[0]) <= 65520 by arithmetic() using { to_integer(b_vec.0[0]) < 65521; };
     have b_vec.0[1] < __rust_checked_9;
     have b_vec.0[1] < 65521u32 by { rewrite(65521u32 == __rust_checked_9); assumption(); }
     apply(uint32_less_than_to_integer(b_vec.0[1], 65521u32)) using { b_vec.0[1] < 65521u32; }
     have to_integer(b_vec.0[1]) <= 65520 by arithmetic() using { to_integer(b_vec.0[1]) < 65521; };
     have b_vec.0[2] < __rust_checked_9;
     have b_vec.0[2] < 65521u32 by { rewrite(65521u32 == __rust_checked_9); assumption(); }
     apply(uint32_less_than_to_integer(b_vec.0[2], 65521u32)) using { b_vec.0[2] < 65521u32; }
     have to_integer(b_vec.0[2]) <= 65520 by arithmetic() using { to_integer(b_vec.0[2]) < 65521; };
     have b_vec.0[3] < __rust_checked_9;
     have b_vec.0[3] < 65521u32 by { rewrite(65521u32 == __rust_checked_9); assumption(); }
     apply(uint32_less_than_to_integer(b_vec.0[3], 65521u32)) using { b_vec.0[3] < 65521u32; }
     have to_integer(b_vec.0[3]) <= 65520 by arithmetic() using { to_integer(b_vec.0[3]) < 65521; };
     have 0 <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by assumption();
     have at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32));
     have 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32)));
     have at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) % 22208 == 0;
     apply(adler_outer_remaining_step(old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)), at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))) using { 0 <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))); }
     apply(adler_outer_remaining_step_divisible(at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))) using { 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))); at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) % 22208 == 0; }
     have (((__rust_mir_27_remaining as u32) as i32)) == at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208;
     have 0 <= (((__rust_mir_27_remaining as u32) as i32)) by { rewrite((((__rust_mir_27_remaining as u32) as i32)) == at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208); assumption(); }
     have (((__rust_mir_27_remaining as u32) as i32)) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by { rewrite((((__rust_mir_27_remaining as u32) as i32)) == at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208); assumption(); }
     have (((__rust_mir_27_remaining as u32) as i32)) % 22208 == 0 by { rewrite((((__rust_mir_27_remaining as u32) as i32)) == at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208); assumption(); }
     have (((__rust_mir_27_remaining as u32) as i32)) < at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) by { rewrite((((__rust_mir_27_remaining as u32) as i32)) == at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208); assumption(); }
     have __rust_mir_27_cursor == at(outer_head, __rust_mir_27_cursor) + 22208;
     apply(adler_outer_cursor_step(old(bytes), old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)), at(outer_head, (((__rust_mir_27_remaining as u32) as i32))))) using { 0 <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); 22208 <= at(outer_head, (((__rust_mir_27_remaining as u32) as i32))); }
     have __rust_mir_27_cursor == old(bytes) + (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - (((__rust_mir_27_remaining as u32) as i32))) by {
      rewrite(__rust_mir_27_cursor == at(outer_head, __rust_mir_27_cursor) + 22208);
      rewrite(at(outer_head, __rust_mir_27_cursor) == old(bytes) + (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - at(outer_head, (((__rust_mir_27_remaining as u32) as i32)))));
      rewrite((((__rust_mir_27_remaining as u32) as i32)) == at(outer_head, (((__rust_mir_27_remaining as u32) as i32))) - 22208);
      assumption();
     }
     mark batch_reduced;
     have truncating_remainder(adler_lane_a(to_integer(at(batch_reduced, a)), to_integer(at(batch_reduced, a_vec.0[0])), to_integer(at(batch_reduced, a_vec.0[1])), to_integer(at(batch_reduced, a_vec.0[2])), to_integer(at(batch_reduced, a_vec.0[3]))), 65521) == adler_spec_a(at(batch_reduced, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(at(batch_reduced, a))) by simp();
     have truncating_remainder(adler_lane_b(to_integer(at(batch_reduced, b)), to_integer(at(batch_reduced, a_vec.0[1])), to_integer(at(batch_reduced, a_vec.0[2])), to_integer(at(batch_reduced, a_vec.0[3])), to_integer(at(batch_reduced, b_vec.0[0])), to_integer(at(batch_reduced, b_vec.0[1])), to_integer(at(batch_reduced, b_vec.0[2])), to_integer(at(batch_reduced, b_vec.0[3]))), 65521) == adler_spec_b(at(batch_reduced, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(at(batch_reduced, a)), old(to_integer((self.b as u32)))) by simp();
     have to_integer(at(batch_reduced, a_vec.0[0])) <= 65520 by simp() using { to_integer(a_vec.0[0]) <= 65520; };
     have to_integer(at(batch_reduced, a_vec.0[1])) <= 65520 by simp() using { to_integer(a_vec.0[1]) <= 65520; };
     have to_integer(at(batch_reduced, a_vec.0[2])) <= 65520 by simp() using { to_integer(a_vec.0[2]) <= 65520; };
     have to_integer(at(batch_reduced, a_vec.0[3])) <= 65520 by simp() using { to_integer(a_vec.0[3]) <= 65520; };
     have to_integer(at(batch_reduced, b_vec.0[0])) <= 65520 by simp() using { to_integer(b_vec.0[0]) <= 65520; };
     have to_integer(at(batch_reduced, b_vec.0[1])) <= 65520 by simp() using { to_integer(b_vec.0[1]) <= 65520; };
     have to_integer(at(batch_reduced, b_vec.0[2])) <= 65520 by simp() using { to_integer(b_vec.0[2]) <= 65520; };
     have to_integer(at(batch_reduced, b_vec.0[3])) <= 65520 by simp() using { to_integer(b_vec.0[3]) <= 65520; };
     execute_until(back_edge());
     have a_vec.0[0] == at(batch_reduced, a_vec.0[0]);
     have to_integer(a_vec.0[0]) <= 65520 by { rewrite(a_vec.0[0] == at(batch_reduced, a_vec.0[0])); assumption(); }
     have a_vec.0[1] == at(batch_reduced, a_vec.0[1]);
     have to_integer(a_vec.0[1]) <= 65520 by { rewrite(a_vec.0[1] == at(batch_reduced, a_vec.0[1])); assumption(); }
     have a_vec.0[2] == at(batch_reduced, a_vec.0[2]);
     have to_integer(a_vec.0[2]) <= 65520 by { rewrite(a_vec.0[2] == at(batch_reduced, a_vec.0[2])); assumption(); }
     have a_vec.0[3] == at(batch_reduced, a_vec.0[3]);
     have to_integer(a_vec.0[3]) <= 65520 by { rewrite(a_vec.0[3] == at(batch_reduced, a_vec.0[3])); assumption(); }
     have b_vec.0[0] == at(batch_reduced, b_vec.0[0]);
     have to_integer(b_vec.0[0]) <= 65520 by { rewrite(b_vec.0[0] == at(batch_reduced, b_vec.0[0])); assumption(); }
     have b_vec.0[1] == at(batch_reduced, b_vec.0[1]);
     have to_integer(b_vec.0[1]) <= 65520 by { rewrite(b_vec.0[1] == at(batch_reduced, b_vec.0[1])); assumption(); }
     have b_vec.0[2] == at(batch_reduced, b_vec.0[2]);
     have to_integer(b_vec.0[2]) <= 65520 by { rewrite(b_vec.0[2] == at(batch_reduced, b_vec.0[2])); assumption(); }
     have b_vec.0[3] == at(batch_reduced, b_vec.0[3]);
     have to_integer(b_vec.0[3]) <= 65520 by { rewrite(b_vec.0[3] == at(batch_reduced, b_vec.0[3])); assumption(); }
     have bytes == old(bytes) by assumption();
     have bytes.len() == old(bytes.len()) by assumption();
     have bytes.len() <= 2147483647u64 by assumption();
     have 0 <= ((bytes.len() as u32) as i32) by assumption();
     have a <= 65520u32 by assumption();
     have b <= 65520u32 by assumption();
     have __rust_mir_27_size == 22208u64 by assumption();
     have __rust_mir_33_live == 0 by assumption();
     have __rust_mir_34_live == 0 by assumption();
     have __rust_mir_36_live == 0 by assumption();
     have 0 <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by assumption();
     have old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) <= ((bytes.len() as u32) as i32) by assumption();
     have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by assumption();
     have 0 <= (((__rust_mir_27_remaining as u32) as i32)) by assumption();
     have (((__rust_mir_27_remaining as u32) as i32)) <= old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by assumption();
     have (((__rust_mir_27_remaining as u32) as i32)) % 22208 == 0 by assumption();
     have __rust_mir_27_cursor == old(bytes) + (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - (((__rust_mir_27_remaining as u32) as i32))) by assumption();
     have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64 by assumption();
     have remainder_len == bytes.len() % 4u64 by assumption();
     have to_integer(a_vec.0[0]) <= 65520 by assumption();
     have to_integer(a_vec.0[1]) <= 65520 by assumption();
     have to_integer(a_vec.0[2]) <= 65520 by assumption();
     have to_integer(a_vec.0[3]) <= 65520 by assumption();
     have to_integer(b_vec.0[0]) <= 65520 by assumption();
     have to_integer(b_vec.0[1]) <= 65520 by assumption();
     have to_integer(b_vec.0[2]) <= 65520 by assumption();
     have to_integer(b_vec.0[3]) <= 65520 by assumption();
     have __rust_mir_27_remaining <= 2147483647u64 by assumption();
     have __rust_mir_27_cursor == bytes + (((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) - __rust_mir_27_remaining) by assumption();
     have forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) } by simp();
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(a)) by {
      rewrite(a == at(batch_reduced, a));
      rewrite(a_vec.0[0] == at(batch_reduced, a_vec.0[0]));
      rewrite(a_vec.0[1] == at(batch_reduced, a_vec.0[1]));
      rewrite(a_vec.0[2] == at(batch_reduced, a_vec.0[2]));
      rewrite(a_vec.0[3] == at(batch_reduced, a_vec.0[3]));
      simp();
     }
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)), to_integer(a), old(to_integer((self.b as u32)))) by simp();
     close_invariants by simp();

     }
     }
     have __rust_mir_27_remaining < 22208u64 by { cases {
      not (0u64 < __rust_mir_27_remaining) => {
       have __rust_mir_27_remaining <= 0u64;
       arithmetic() using { __rust_mir_27_remaining <= 0u64; }
      }
      not (__rust_mir_27_size <= __rust_mir_27_remaining) => {
       have __rust_mir_27_remaining < __rust_mir_27_size;
       rewrite(22208u64 == __rust_mir_27_size); assumption();
      }
     } }
     have __rust_mir_27_remaining <= 22207u64 by arithmetic() using { __rust_mir_27_remaining < 22208u64; };
     apply(adler_bounded_count_upper(__rust_mir_27_remaining, 22207));
     have not (((__rust_mir_27_size as u32) as i32) <= (((__rust_mir_27_remaining as u32) as i32))) by {
      rewrite(__rust_mir_27_size == 22208u64);
      arithmetic() using { (((__rust_mir_27_remaining as u32) as i32)) <= 22207; }
     }
     have not (0 < (((__rust_mir_27_remaining as u32) as i32))) or not (((__rust_mir_27_size as u32) as i32) <= (((__rust_mir_27_remaining as u32) as i32))) by assumption();
     apply(adler_outer_exhausted_remaining((((__rust_mir_27_remaining as u32) as i32)), __rust_mir_27_size)) using { 0 <= (((__rust_mir_27_remaining as u32) as i32)); (((__rust_mir_27_remaining as u32) as i32)) % 22208 == 0; __rust_mir_27_size == 22208u64; not (0 < (((__rust_mir_27_remaining as u32) as i32))) or not (((__rust_mir_27_size as u32) as i32) <= (((__rust_mir_27_remaining as u32) as i32))); }
     apply(adler_bounded_count(__rust_mir_27_remaining));
     have __rust_mir_27_remaining == 0u64 by {
      rewrite(__rust_mir_27_remaining == (((__rust_mir_27_remaining as u32) as i32) as usize));
      rewrite((((__rust_mir_27_remaining as u32) as i32)) == 0); normalize();
     }
     have __rust_mir_27_cursor == old(bytes) + old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by { rewrite(__rust_mir_27_cursor == old(bytes) + (old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) - (((__rust_mir_27_remaining as u32) as i32)))); rewrite((((__rust_mir_27_remaining as u32) as i32)) == 0); normalize(); }
     have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(((__rust_mir_27_remaining as u32) as i32) == 0); normalize(); }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), to_integer(a)) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)); simp(); }
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) - ((__rust_mir_27_remaining as u32) as i32)); simp(); }
     apply(adler_general_bounded_native_prefix(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_general_native_bounded_prefix_divisible(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_outer_remainder_native_bound(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; }
     apply(adler_outer_remainder_signed_bound(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; }
     apply(adler_outer_remainder_signed_divisible(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; }
     have remainder_chunk_len <= 22204u64 by { rewrite(remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64); assumption(); }
     have remainder_chunk_len <= 2147483647u64 by normalize() using { remainder_chunk_len <= 22204u64; };
     have remainder_chunk == old(bytes) + old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) by assumption();
     have ((remainder_chunk_len as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64); normalize(); }
     have 0 <= ((remainder_chunk_len as u32) as i32) by { rewrite(((remainder_chunk_len as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); assumption(); }
     apply(adler_general_bounded_prefix_within_full(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_outer_signed_partition_identity(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; }
     have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by simp() using { bytes.len() == old(bytes.len()); };
     have defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); rewrite(((remainder_chunk_len as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); assumption(); }
     have (((bytes.len() - bytes.len() % 4u64) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); rewrite(((remainder_chunk_len as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); assumption(); }
     have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32) by simp() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32); };
     have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) <= ((bytes.len() as u32) as i32) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32)); assumption(); }
     have 0 <= ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); assumption(); }
     apply(int32_add_to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), ((remainder_chunk_len as u32) as i32))) using { defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)); }
     apply(int32_less_equal_to_integer(0, ((remainder_chunk_len as u32) as i32))) using { 0 <= ((remainder_chunk_len as u32) as i32); }
     have to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) <= to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)) by { rewrite(to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)) == to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + to_integer(((remainder_chunk_len as u32) as i32))); arithmetic() using { to_integer(0) <= to_integer(((remainder_chunk_len as u32) as i32)); } }
     apply(int32_to_integer_less_equal_implies_less_equal(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32))) using { to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) <= to_integer(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)); }

     have remainder_chunk == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(bytes == old(bytes)); rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) == old(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32))); assumption(); }
     apply(adler_outer_remainder_divisible(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; }
     have remainder_chunk_len % 4u64 == 0u64 by { rewrite(remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64); assumption(); }
     mark remainder_ctor;
     execute_until(assignment(__rust_mir_60_tail, 0));
     have __rust_checked_90 == remainder_chunk;
     have __rust_checked_91 == remainder_chunk_len;
     have __rust_mir_60_size == 4u64;
     have __rust_mir_60_tail_len == 0u64 by simp() using { __rust_checked_91 == remainder_chunk_len; __rust_mir_60_size == 4u64; remainder_chunk_len % 4u64 == 0u64; };
     have (((__rust_mir_60_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32) by simp() using { __rust_checked_91 == remainder_chunk_len; __rust_mir_60_tail_len == 0u64; };
     have __rust_checked_90 == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(__rust_checked_90 == remainder_chunk); assumption(); }
     have 0 <= (((__rust_mir_60_remaining as u32) as i32)) by { rewrite((((__rust_mir_60_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); assumption(); }
     have defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((__rust_mir_60_remaining as u32) as i32))) by { rewrite((((__rust_mir_60_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); assumption(); }
     have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((__rust_mir_60_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32) by { rewrite((((__rust_mir_60_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); assumption(); }

     have __rust_checked_94 != 0u64 by simp() using { __rust_checked_94 == 22208u64; };
     have (((__rust_checked_93 - __rust_checked_93 % __rust_checked_94) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(__rust_checked_93 == bytes.len() - bytes.len() % 4u64); rewrite(__rust_checked_94 == 22208u64); normalize(); }
     have 0 <= ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32)); assumption(); }
     have defined((((__rust_checked_93 - __rust_checked_93 % __rust_checked_94) as u32) as i32) + (((__rust_mir_60_remaining as u32) as i32))) by { rewrite((((__rust_checked_93 - __rust_checked_93 % __rust_checked_94) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); rewrite((((__rust_mir_60_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); assumption(); }
     have 0 <= (((__rust_checked_93 - __rust_checked_93 % __rust_checked_94) as u32) as i32) + (((__rust_mir_60_remaining as u32) as i32)) by { rewrite((((__rust_checked_93 - __rust_checked_93 % __rust_checked_94) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); rewrite((((__rust_mir_60_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); assumption(); }
     have (((__rust_checked_93 - __rust_checked_93 % __rust_checked_94) as u32) as i32) + (((__rust_mir_60_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32) by { rewrite((((__rust_checked_93 - __rust_checked_93 % __rust_checked_94) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); rewrite((((__rust_mir_60_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); assumption(); }
     step();
     execute_until(loop(2));
     have (((__rust_mir_62_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32);
     have __rust_mir_62_cursor == remainder_chunk;
     have __rust_mir_62_size == 4u64;
     have ((remainder_chunk_len as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64); normalize(); }
     have 0 <= ((remainder_chunk_len as u32) as i32) by { rewrite(((remainder_chunk_len as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); assumption(); }
     have ((remainder_chunk_len as u32) as i32) <= 22204 by { rewrite(((remainder_chunk_len as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); assumption(); }
     have (((remainder_chunk_len as u32) as i32)) % 4 == 0 by { rewrite(((remainder_chunk_len as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); assumption(); }
     apply(adler_lane_initial_ceiling());
     apply(adler_lane_iterator_initial(((remainder_chunk_len as u32) as i32)));
     have adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))) == 0 by { rewrite((((__rust_mir_62_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); assumption(); }
     have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec.0[0]) <= 65520; } }
     have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec.0[0]) <= 65520; } }
     have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec.0[1]) <= 65520; } }
     have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec.0[1]) <= 65520; } }
     have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec.0[2]) <= 65520; } }
     have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec.0[2]) <= 65520; } }
     have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec.0[3]) <= 65520; } }
     have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by { rewrite(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec.0[3]) <= 65520; } }
     have 0 <= (((__rust_mir_62_remaining as u32) as i32)) by { rewrite((((__rust_mir_62_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); assumption(); }
     have (((__rust_mir_62_remaining as u32) as i32)) <= ((remainder_chunk_len as u32) as i32) by { rewrite((((__rust_mir_62_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); normalize() using {}; }
     have 0 <= (((__rust_mir_62_remaining as u32) as i32)) and (((__rust_mir_62_remaining as u32) as i32)) <= ((remainder_chunk_len as u32) as i32) by assumption();
     have (((__rust_mir_62_remaining as u32) as i32)) % 4 == 0 by { rewrite((((__rust_mir_62_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); assumption(); }
     have __rust_mir_62_cursor == remainder_chunk + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32))) by { rewrite((((__rust_mir_62_remaining as u32) as i32)) == ((remainder_chunk_len as u32) as i32)); simp(); }
     have bytes.len() == old(bytes.len()) by assumption();
     have __rust_mir_60_remaining == remainder_chunk_len by simp() using { __rust_checked_91 == remainder_chunk_len; __rust_mir_60_tail_len == 0u64; };
     have __rust_mir_62_remaining == __rust_mir_60_remaining;
     have __rust_mir_62_remaining == remainder_chunk_len by simp() using { __rust_mir_62_remaining == __rust_mir_60_remaining; __rust_mir_60_remaining == remainder_chunk_len; };
     have __rust_mir_62_remaining <= 22208u64 by arithmetic() using { __rust_mir_62_remaining == remainder_chunk_len; remainder_chunk_len <= 22204u64; };
     apply(adler_bounded_count(remainder_chunk_len));
     have __rust_mir_62_cursor == remainder_chunk;
     have __rust_mir_62_cursor == remainder_chunk + (remainder_chunk_len - __rust_mir_62_remaining) by {
      apply(adler_uint64_self_subtract(remainder_chunk_len)); rewrite(__rust_mir_62_remaining == remainder_chunk_len); rewrite(remainder_chunk_len - remainder_chunk_len == 0u64); simp() using { __rust_mir_62_cursor == remainder_chunk; }
     }
     have __rust_mir_62_remaining <= remainder_chunk_len by { rewrite(__rust_mir_62_remaining == remainder_chunk_len); normalize(); }
     have (bytes.len() - bytes.len() % 4u64) <= bytes.len() by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); };
     have (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64) by normalize();
     have ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= (bytes.len() - bytes.len() % 4u64) by arithmetic() using { (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64); bytes.len() % 4u64 <= bytes.len(); };
     have ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= bytes.len() by arithmetic() using { ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= (bytes.len() - bytes.len() % 4u64); (bytes.len() - bytes.len() % 4u64) <= bytes.len(); (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64); bytes.len() % 4u64 <= bytes.len(); };
     have ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= 2147483647u64 by arithmetic() using { ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) <= bytes.len(); bytes.len() <= 2147483647u64; (bytes.len() - bytes.len() % 4u64) % 22208u64 <= (bytes.len() - bytes.len() % 4u64); bytes.len() % 4u64 <= bytes.len(); };
     apply(adler_bounded_pointer_index(bytes, ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)));
     have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) by simp() using { remainder_chunk == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32); bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32); };
     have ((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining) == ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) by { rewrite(__rust_mir_62_remaining == remainder_chunk_len); rewrite(remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64); normalize(); }
     have __rust_mir_62_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining) by { rewrite(((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining) == ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); simp() using { __rust_mir_62_cursor == remainder_chunk; remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64); } }
     have __rust_mir_62_remaining <= (bytes.len() - bytes.len() % 4u64) by { rewrite(__rust_mir_62_remaining == remainder_chunk_len); rewrite(remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64); assumption(); }
     apply(uint32_to_integer_bounds(b));
     apply(uint32_to_integer_bounds(b_vec.0[0]));
     apply(uint32_to_integer_bounds(b_vec.0[1]));
     apply(uint32_to_integer_bounds(b_vec.0[2]));
     apply(uint32_to_integer_bounds(b_vec.0[3]));
     apply(adler_canonical_lane_b_floor(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]))) using { 0 <= to_integer(b); to_integer(a_vec.0[1]) <= 65520; to_integer(a_vec.0[2]) <= 65520; to_integer(a_vec.0[3]) <= 65520; 0 <= to_integer(b_vec.0[0]); 0 <= to_integer(b_vec.0[1]); 0 <= to_integer(b_vec.0[2]); 0 <= to_integer(b_vec.0[3]); }
     apply(adler_empty_remainder_position(((remainder_chunk_len as u32) as i32), ((__rust_mir_62_remaining as u32) as i32))) using { 0 <= ((remainder_chunk_len as u32) as i32); ((__rust_mir_62_remaining as u32) as i32) == ((remainder_chunk_len as u32) as i32); }
     have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == 0); simp(); }
     // The remainder starts at the already proved full-batch prefix.
     apply(adler_defined_add_zero(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)));
     have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by { rewrite(((__rust_mir_62_remaining as u32) as i32) == ((remainder_chunk_len as u32) as i32)); simp(); }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))), to_integer(a)) by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); simp(); }
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)); rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == 0); simp(); }
     loop {
      decreases (((__rust_mir_62_remaining as u32) as i32));
     invariant __rust_mir_62_remaining <= 22208u64;
      owns a_vec.0[0..4];
      owns b_vec.0[0..4];
      views *bytes;

      invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))), to_integer(a));
      invariant 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
      invariant truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))), to_integer(a), old(to_integer((self.b as u32))));
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant __rust_mir_62_cursor == remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32));
      invariant remainder_chunk == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32);
      invariant forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) };
      invariant __rust_mir_62_remaining <= remainder_chunk_len;
      invariant remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64);
      invariant __rust_mir_62_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining);
      invariant __rust_mir_62_remaining <= (bytes.len() - bytes.len() % 4u64);
      invariant (bytes.len() - bytes.len() % 4u64) <= bytes.len();
      invariant bytes.len() % 4u64 <= bytes.len();
      invariant bytes == old(bytes);
      invariant bytes.len() == old(bytes.len());
      invariant a <= 65520u32;
      invariant b <= 65520u32;
      invariant 0 <= ((remainder_chunk_len as u32) as i32);
      invariant ((remainder_chunk_len as u32) as i32) <= 22204;
      invariant ((remainder_chunk_len as u32) as i32) % 4 == 0;
      invariant __rust_mir_62_size == 4u64;
      invariant 0 <= (((__rust_mir_62_remaining as u32) as i32)) and (((__rust_mir_62_remaining as u32) as i32)) <= ((remainder_chunk_len as u32) as i32);
      invariant (((__rust_mir_62_remaining as u32) as i32)) % 4 == 0;
      invariant to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))));
      invariant to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))));
      invariant to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))));
      invariant to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))));
      invariant to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))));
      invariant to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))));
      invariant to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))));
      invariant to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32))));
      invariant bytes.len() <= 2147483647u64;
      invariant 0 <= ((bytes.len() as u32) as i32);
      invariant 0 <= ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32);
      invariant defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32));
      invariant ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) <= ((bytes.len() as u32) as i32);
      invariant remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64;
      invariant remainder_len == bytes.len() % 4u64;
      preserve by {
       have 4u64 <= __rust_mir_62_remaining;
       have (remainder_chunk_len - __rust_mir_62_remaining) + 4u64 <= remainder_chunk_len by arithmetic() using {
        __rust_mir_62_remaining <= remainder_chunk_len; 4u64 <= __rust_mir_62_remaining;
       };
       have 4 <= (((__rust_mir_62_remaining as u32) as i32)) by {
        have __rust_mir_62_remaining <= 2147483647u64 by arithmetic() using { __rust_mir_62_remaining <= 22208u64; };
        apply(adler_bounded_count_lower(__rust_mir_62_remaining, 4)); assumption();
       }
       have 4u64 <= __rust_mir_62_remaining;
       have ((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining) <= (bytes.len() - bytes.len() % 4u64) by arithmetic() using { __rust_mir_62_remaining <= (bytes.len() - bytes.len() % 4u64); bytes.len() % 4u64 <= bytes.len(); };
       have ((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining) <= bytes.len() by arithmetic() using { ((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining) <= (bytes.len() - bytes.len() % 4u64); (bytes.len() - bytes.len() % 4u64) <= bytes.len(); __rust_mir_62_remaining <= (bytes.len() - bytes.len() % 4u64); bytes.len() % 4u64 <= bytes.len(); };
       have 4u64 <= bytes.len() - ((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining) by arithmetic() using { 4u64 <= __rust_mir_62_remaining; __rust_mir_62_remaining <= (bytes.len() - bytes.len() % 4u64); (bytes.len() - bytes.len() % 4u64) <= bytes.len(); bytes.len() % 4u64 <= bytes.len(); };
       mark lane_head;
       have at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) % 4 == 0;
       have at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32);
       have 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32)));
       have 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32)));
       have ((remainder_chunk_len as u32) as i32) <= 22208 by arithmetic() using { ((remainder_chunk_len as u32) as i32) <= 22204; };

       have 0 <= ((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { 0 <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); };
       have (((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))) + 4 <= ((remainder_chunk_len as u32) as i32) by arithmetic() using { 0 <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); };
       have (((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))) <= 22204 by arithmetic() using { 0 <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); };
       apply(adler_bounded_slice_access(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), (((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))), ((remainder_chunk_len as u32) as i32), ((bytes.len() as u32) as i32))) using { 0 <= ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32); 0 <= (((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))); (((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))) <= 22204; (((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))) + 4 <= ((remainder_chunk_len as u32) as i32); defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)); ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) <= ((bytes.len() as u32) as i32); }
       execute_until(assignment(__rust_mir_69, 0)); step();
       have __rust_mir_69 == at(lane_head, __rust_mir_62_cursor);
       execute_until(assignment(__rust_mir_69_len, 0)); step();
       have __rust_mir_69_len == 4u64;
       have (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4;
       have (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4) == (((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
       have 0 <= (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4) by { rewrite((((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4) == (((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); assumption(); }
       have (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4) <= 22204 by { rewrite((((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4) == (((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); assumption(); }
       have 0 <= (((__rust_mir_62_remaining as u32) as i32)) by arithmetic() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); };
       have (((__rust_mir_62_remaining as u32) as i32)) <= ((remainder_chunk_len as u32) as i32) by arithmetic() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
       have __rust_mir_69 == remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) by {
        rewrite((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) == (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        simp() using { __rust_mir_69 == at(lane_head, __rust_mir_62_cursor); at(lane_head, __rust_mir_62_cursor) == remainder_chunk + (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))); }
       }
       apply(adler_current_window(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) using { 0 <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 0 <= (((__rust_mir_62_remaining as u32) as i32)); (((__rust_mir_62_remaining as u32) as i32)) <= ((remainder_chunk_len as u32) as i32); }
       apply(adler_bounded_slice_access(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4), ((remainder_chunk_len as u32) as i32), ((bytes.len() as u32) as i32))) using { 0 <= ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32); 0 <= (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4); (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4) <= 22204; (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4) + 4 <= ((remainder_chunk_len as u32) as i32); defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)); ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) <= ((bytes.len() as u32) as i32); }

       have defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4)) by assumption();
       apply(adler_pointer_sum_association(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4))) using { defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4)); }

       have defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4)) + 4) by assumption();
       apply(int32_add_to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4)), 4)) using { defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4)) + 4); }
       have to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4))) <= to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4)) + 4) by { rewrite(to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4)) + 4) == to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4))) + to_integer(4)); arithmetic() using {}; }
       apply(int32_to_integer_less_equal_implies_less_equal((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4)), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4)) + 4)) using { to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4))) <= to_integer((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) - 4)) + 4); }

       mark byte_view;
       execute_until(assignment(__rust_mir_68, 0));
       have __rust_checked_22 == __rust_mir_69;
       have __rust_checked_22 == at(byte_view, __rust_mir_69);
       have __rust_mir_69 == at(lane_head, __rust_mir_62_cursor);
       have at(lane_head, __rust_mir_62_cursor) == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) by assumption();
       have __rust_checked_22 == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) by simp() using { __rust_checked_22 == __rust_mir_69; __rust_mir_69 == at(lane_head, __rust_mir_62_cursor); at(lane_head, __rust_mir_62_cursor) == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)); };

       have ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) <= (bytes.len() - bytes.len() % 4u64) by arithmetic() using { at(lane_head, __rust_mir_62_remaining) <= (bytes.len() - bytes.len() % 4u64); bytes.len() % 4u64 <= bytes.len(); };
       have ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) <= bytes.len() by arithmetic() using { ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) <= (bytes.len() - bytes.len() % 4u64); (bytes.len() - bytes.len() % 4u64) <= bytes.len(); at(lane_head, __rust_mir_62_remaining) <= (bytes.len() - bytes.len() % 4u64); bytes.len() % 4u64 <= bytes.len(); };
       have 4u64 <= bytes.len() - ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) by arithmetic() using { 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= (bytes.len() - bytes.len() % 4u64); (bytes.len() - bytes.len() % 4u64) <= bytes.len(); bytes.len() % 4u64 <= bytes.len(); };
       mark remainder_constructor;
       step();
       execute_until(assignment(__rust_mir_71, 0));
       mark vector_a;
       apply(adler_checked_four_byte_start((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)))) using { defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 4); }
       // Use the checked constructor's exact call-entry byte observations.
       have at(remainder_constructor, __rust_checked_22) == (bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) by simp() using { __rust_checked_22 == __rust_mir_69; __rust_mir_69 == remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4); remainder_chunk == bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32); };
       have to_integer(at(vector_a, __rust_mir_68.0[0])) == at(remainder_constructor, to_integer((__rust_checked_22[0] as i32))) by normalize() using { to_integer(__rust_mir_68.0[0]) == at(remainder_constructor, to_integer((__rust_checked_22[0] as i32))); };
       have at(remainder_constructor, (__rust_checked_22[0] as i32)) == at(remainder_constructor, (((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[0] as i32)) by {
        rewrite(at(remainder_constructor, __rust_checked_22) == (bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)); simp();
       }
       apply(adler_checked_chunk_byte_observation(at(remainder_constructor, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4), 0)) using { defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))); 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) <= 2147483643; 0 <= 0; 0 <= 3; }
       have to_integer(at(vector_a, __rust_mir_68.0[0])) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 0)] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_68.0[0])) == at(remainder_constructor, to_integer((__rust_checked_22[0] as i32))));
        rewrite(at(remainder_constructor, (__rust_checked_22[0] as i32)) == at(remainder_constructor, (((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[0] as i32)));
        normalize() using { at(remainder_constructor, to_integer((((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[0] as i32))) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 0)] as i32))); }
       }
       have at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 0)] as i32))) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 0)] as i32))) by simp();
       have to_integer(at(vector_a, __rust_mir_68.0[0])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 0)] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_68.0[0])) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 0)] as i32)))); assumption();
       }
       have to_integer(at(vector_a, __rust_mir_68.0[1])) == at(remainder_constructor, to_integer((__rust_checked_22[1] as i32))) by normalize() using { to_integer(__rust_mir_68.0[1]) == at(remainder_constructor, to_integer((__rust_checked_22[1] as i32))); };
       have at(remainder_constructor, (__rust_checked_22[1] as i32)) == at(remainder_constructor, (((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[1] as i32)) by {
        rewrite(at(remainder_constructor, __rust_checked_22) == (bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)); simp();
       }
       apply(adler_checked_chunk_byte_observation(at(remainder_constructor, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4), 1)) using { defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))); 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) <= 2147483643; 0 <= 1; 1 <= 3; }
       have to_integer(at(vector_a, __rust_mir_68.0[1])) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 1)] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_68.0[1])) == at(remainder_constructor, to_integer((__rust_checked_22[1] as i32))));
        rewrite(at(remainder_constructor, (__rust_checked_22[1] as i32)) == at(remainder_constructor, (((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[1] as i32)));
        normalize() using { at(remainder_constructor, to_integer((((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[1] as i32))) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 1)] as i32))); }
       }
       have at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 1)] as i32))) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 1)] as i32))) by simp();
       have to_integer(at(vector_a, __rust_mir_68.0[1])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 1)] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_68.0[1])) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 1)] as i32)))); assumption();
       }
       have to_integer(at(vector_a, __rust_mir_68.0[2])) == at(remainder_constructor, to_integer((__rust_checked_22[2] as i32))) by normalize() using { to_integer(__rust_mir_68.0[2]) == at(remainder_constructor, to_integer((__rust_checked_22[2] as i32))); };
       have at(remainder_constructor, (__rust_checked_22[2] as i32)) == at(remainder_constructor, (((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[2] as i32)) by {
        rewrite(at(remainder_constructor, __rust_checked_22) == (bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)); simp();
       }
       apply(adler_checked_chunk_byte_observation(at(remainder_constructor, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4), 2)) using { defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))); 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) <= 2147483643; 0 <= 2; 2 <= 3; }
       have to_integer(at(vector_a, __rust_mir_68.0[2])) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 2)] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_68.0[2])) == at(remainder_constructor, to_integer((__rust_checked_22[2] as i32))));
        rewrite(at(remainder_constructor, (__rust_checked_22[2] as i32)) == at(remainder_constructor, (((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[2] as i32)));
        normalize() using { at(remainder_constructor, to_integer((((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[2] as i32))) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 2)] as i32))); }
       }
       have at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 2)] as i32))) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 2)] as i32))) by simp();
       have to_integer(at(vector_a, __rust_mir_68.0[2])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 2)] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_68.0[2])) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 2)] as i32)))); assumption();
       }
       have to_integer(at(vector_a, __rust_mir_68.0[3])) == at(remainder_constructor, to_integer((__rust_checked_22[3] as i32))) by normalize() using { to_integer(__rust_mir_68.0[3]) == at(remainder_constructor, to_integer((__rust_checked_22[3] as i32))); };
       have at(remainder_constructor, (__rust_checked_22[3] as i32)) == at(remainder_constructor, (((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[3] as i32)) by {
        rewrite(at(remainder_constructor, __rust_checked_22) == (bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)); simp();
       }
       apply(adler_checked_chunk_byte_observation(at(remainder_constructor, bytes), ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4), 3)) using { defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))); 0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) <= 2147483643; 0 <= 3; 3 <= 3; }
       have to_integer(at(vector_a, __rust_mir_68.0[3])) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 3)] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_68.0[3])) == at(remainder_constructor, to_integer((__rust_checked_22[3] as i32))));
        rewrite(at(remainder_constructor, (__rust_checked_22[3] as i32)) == at(remainder_constructor, (((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[3] as i32)));
        normalize() using { at(remainder_constructor, to_integer((((bytes + ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32)) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))[3] as i32))) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 3)] as i32))); }
       }
       have at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 3)] as i32))) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 3)] as i32))) by simp();
       have to_integer(at(vector_a, __rust_mir_68.0[3])) == at(vector_a, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 3)] as i32))) by {
        rewrite(to_integer(at(vector_a, __rust_mir_68.0[3])) == at(remainder_constructor, to_integer((bytes[((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 3)] as i32)))); assumption();
       }
       apply(uint32_to_integer_bounds(at(vector_a, a_vec.0[0])));
       apply(uint32_to_integer_bounds(at(vector_a, b_vec.0[0])));
       apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68.0[0])));
       have 0 <= to_integer(at(vector_a, a_vec.0[0]));
       have 0 <= to_integer(at(vector_a, b_vec.0[0]));
       have to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))));
       have to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))));
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[0]));
       have to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255;
       apply(adler_lane_iterator_add_contracts(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_68.0[0]))) using { 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[0])); to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[0])); to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255; }
       apply(adler_lane_iterator_native_preservation(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_68.0[0]))) using { 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[0])); to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[0])); to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255; }
       apply(uint32_to_integer_bounds(at(vector_a, a_vec.0[1])));
       apply(uint32_to_integer_bounds(at(vector_a, b_vec.0[1])));
       apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68.0[1])));
       have 0 <= to_integer(at(vector_a, a_vec.0[1]));
       have 0 <= to_integer(at(vector_a, b_vec.0[1]));
       have to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))));
       have to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))));
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[1]));
       have to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255;
       apply(adler_lane_iterator_add_contracts(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_68.0[1]))) using { 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[1])); to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[1])); to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255; }
       apply(adler_lane_iterator_native_preservation(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_68.0[1]))) using { 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[1])); to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[1])); to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255; }
       apply(uint32_to_integer_bounds(at(vector_a, a_vec.0[2])));
       apply(uint32_to_integer_bounds(at(vector_a, b_vec.0[2])));
       apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68.0[2])));
       have 0 <= to_integer(at(vector_a, a_vec.0[2]));
       have 0 <= to_integer(at(vector_a, b_vec.0[2]));
       have to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))));
       have to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))));
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[2]));
       have to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255;
       apply(adler_lane_iterator_add_contracts(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_68.0[2]))) using { 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[2])); to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[2])); to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255; }
       apply(adler_lane_iterator_native_preservation(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_68.0[2]))) using { 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[2])); to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[2])); to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255; }
       apply(uint32_to_integer_bounds(at(vector_a, a_vec.0[3])));
       apply(uint32_to_integer_bounds(at(vector_a, b_vec.0[3])));
       apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68.0[3])));
       have 0 <= to_integer(at(vector_a, a_vec.0[3]));
       have 0 <= to_integer(at(vector_a, b_vec.0[3]));
       have to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))));
       have to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))));
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[3]));
       have to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255;
       apply(adler_lane_iterator_add_contracts(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[3]))) using { 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[3])); to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[3])); to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255; }
       apply(adler_lane_iterator_native_preservation(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[3]))) using { 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22208; 0 <= to_integer(at(vector_a, a_vec.0[3])); to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, b_vec.0[3])); to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))); 0 <= to_integer(at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255; }
       have (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) == (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { ((__rust_mir_62_remaining as u32) as i32) == at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4; 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
       have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) == (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by { rewrite((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) == (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); normalize(); }
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)), to_integer(a)) by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) == (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))))); simp(); }
       apply(uint32_to_integer_bounds(a));
       apply(uint32_less_equal_to_integer(a, 65520u32)) using { a <= 65520u32; }
       have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) by { have to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) == to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) by simp() using { (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) == ((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); }; rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) == to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); simp(); }
       apply(uint32_add_to_integer(at(vector_a, a_vec.0[0]), at(vector_a, __rust_mir_68.0[0]))) using { to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) <= 4294967295; }
       have to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))); assumption(); }
       apply(uint32_add_to_integer(at(vector_a, a_vec.0[1]), at(vector_a, __rust_mir_68.0[1]))) using { to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) <= 4294967295; }
       have to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))); assumption(); }
       apply(uint32_add_to_integer(at(vector_a, a_vec.0[2]), at(vector_a, __rust_mir_68.0[2]))) using { to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) <= 4294967295; }
       have to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))); assumption(); }
       apply(uint32_add_to_integer(at(vector_a, a_vec.0[3]), at(vector_a, __rust_mir_68.0[3]))) using { to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) <= 4294967295; }
       have to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3]))) <= 4294967295 by { rewrite(to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))); assumption(); }
       apply(adler_native_deferred_b_step((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[0]), at(vector_a, __rust_mir_68.0[1]), at(vector_a, __rust_mir_68.0[2]), at(vector_a, __rust_mir_68.0[3]))) using { 0 <= (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4); (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) <= 22204; 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) <= 4294967295; to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3]))) <= 4294967295; }
       apply(adler_nonnegative_deferred_b_step((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[0]), at(vector_a, __rust_mir_68.0[1]), at(vector_a, __rust_mir_68.0[2]), at(vector_a, __rust_mir_68.0[3]))) using { 0 <= (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4); (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) <= 22204; 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) <= 4294967295; to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2]))) <= 4294967295; to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3]))) <= 4294967295; }
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)), to_integer(at(vector_a, a)), old(to_integer((self.b as u32)))) by { have to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) == to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) by simp() using { (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) == ((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); }; rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) == (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))))); rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) == to_integer(((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); simp(); }
       apply(adler_native_deferred_b_prefix_step(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)), (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4), to_integer(a), old(to_integer((self.b as u32))), a, b, at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[0]), at(vector_a, b_vec.0[1]), at(vector_a, b_vec.0[2]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[0]), at(vector_a, __rust_mir_68.0[1]), at(vector_a, __rust_mir_68.0[2]), at(vector_a, __rust_mir_68.0[3]))) using {
        0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) <= 2147483643;
        0 <= to_integer(a); to_integer(a) <= 65520;
        truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)), to_integer(a));
        to_integer(at(vector_a, __rust_mir_68.0[0])) == at(vector_a, to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))] as i32)));
        to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_68.0[1])) == at(vector_a, to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 1] as i32)));
        to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_68.0[2])) == at(vector_a, to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 2] as i32)));
        to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_68.0[3])) == at(vector_a, to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 3] as i32)));
        to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) <= 4294967295;
        0 <= (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4); (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) <= 22204; 0 <= old(to_integer((self.b as u32))); 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)), to_integer(at(vector_a, a)), old(to_integer((self.b as u32)))); to_integer(at(vector_a, b_vec.0[0])) + (to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[1])) + (to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[2])) + (to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2]))) <= 4294967295; to_integer(at(vector_a, b_vec.0[3])) + (to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3]))) <= 4294967295;
       }
       apply(adler_native_four_lane_a_prefix_step(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)), to_integer(a), to_integer(a), at(vector_a, a_vec.0[0]), at(vector_a, a_vec.0[1]), at(vector_a, a_vec.0[2]), at(vector_a, a_vec.0[3]), at(vector_a, __rust_mir_68.0[0]), at(vector_a, __rust_mir_68.0[1]), at(vector_a, __rust_mir_68.0[2]), at(vector_a, __rust_mir_68.0[3]))) using {
        0 <= (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)); (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) <= 2147483643;
        0 <= to_integer(a); to_integer(a) <= 65520;
        truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a(at(vector_a, bytes), (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)), to_integer(a));
        to_integer(at(vector_a, __rust_mir_68.0[0])) == at(vector_a, to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))] as i32)));
        to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_68.0[1])) == at(vector_a, to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 1] as i32)));
        to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_68.0[2])) == at(vector_a, to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 2] as i32)));
        to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])) <= 4294967295;
        to_integer(at(vector_a, __rust_mir_68.0[3])) == at(vector_a, to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 3] as i32)));
        to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])) <= 4294967295;
       }
       execute_until(assignment(__rust_mir_74, 0));
       have a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]);
       have b_vec.0[0] == at(vector_a, b_vec.0[0]);
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]); };
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) by simp() using { a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]); };
       have to_integer(b_vec.0[0]) + to_integer(a_vec.0[0]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])); to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) <= 4294967295; };
       have a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]);
       have b_vec.0[1] == at(vector_a, b_vec.0[1]);
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]); };
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]); };
       have to_integer(b_vec.0[1]) + to_integer(a_vec.0[1]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) <= 4294967295; };
       have a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]);
       have b_vec.0[2] == at(vector_a, b_vec.0[2]);
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]); };
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]); };
       have to_integer(b_vec.0[2]) + to_integer(a_vec.0[2]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) <= 4294967295; };
       have a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]);
       have b_vec.0[3] == at(vector_a, b_vec.0[3]);
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]); };
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]); };
       have to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) <= 4294967295; };
       mark vector_b;
       execute_until(back_edge());
       have a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]);
       have b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]));
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) by simp() using { a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; };
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); };
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; };
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); };
       have a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]);
       have b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]));
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; };
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); };
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; };
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); };
       have a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]);
       have b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]));
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; };
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); };
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; };
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); };
       have a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]);
       have b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]));
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; };
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); };
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)) by simp() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; };
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4)); };
       have 0 <= (((__rust_mir_62_remaining as u32) as i32)) by arithmetic() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); };
       have (((__rust_mir_62_remaining as u32) as i32)) <= ((remainder_chunk_len as u32) as i32) by arithmetic() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
       have 0 <= (((__rust_mir_62_remaining as u32) as i32)) and (((__rust_mir_62_remaining as u32) as i32)) <= ((remainder_chunk_len as u32) as i32) by assumption();
       have (((__rust_mir_62_remaining as u32) as i32)) % 4 == 0 by { rewrite((((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4); normalize() using { at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) % 4 == 0; 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; } }
       have __rust_mir_62_cursor == at(lane_head, __rust_mir_62_cursor) + 4;
       have (((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))) + 4 == ((remainder_chunk_len as u32) as i32) - (((__rust_mir_62_remaining as u32) as i32)) by arithmetic() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
       have 0 <= ((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
       have ((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= 22200 by arithmetic() using { 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
       have ((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= 22204 by arithmetic() using { ((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= 22200; };
       have 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); };
       have defined(((remainder_chunk_len as u32) as i32) - at(lane_head, (((__rust_mir_62_remaining as u32) as i32)))) by apply(int32_nonnegative_subtract_within_value_is_defined(((remainder_chunk_len as u32) as i32), at(lane_head, (((__rust_mir_62_remaining as u32) as i32))))) using { 0 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); };


       have (((__rust_mir_62_remaining as u32) as i32)) < at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { (((__rust_mir_62_remaining as u32) as i32)) == at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) - 4; 4 <= at(lane_head, (((__rust_mir_62_remaining as u32) as i32))); at(lane_head, (((__rust_mir_62_remaining as u32) as i32))) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
       have bytes == old(bytes) by assumption();
       have bytes.len() == old(bytes.len()) by assumption();
       have a <= 65520u32 by assumption();
       have b <= 65520u32 by assumption();
       have 0 <= ((remainder_chunk_len as u32) as i32) by assumption();
       have ((remainder_chunk_len as u32) as i32) <= 22204 by assumption();
       have ((remainder_chunk_len as u32) as i32) % 4 == 0 by assumption();
       have __rust_mir_62_size == 4u64 by assumption();
       have 0 <= (((__rust_mir_62_remaining as u32) as i32)) and (((__rust_mir_62_remaining as u32) as i32)) <= ((remainder_chunk_len as u32) as i32) by assumption();
       have (((__rust_mir_62_remaining as u32) as i32)) % 4 == 0 by assumption();

       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by assumption();
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by assumption();
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by assumption();
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by assumption();
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by assumption();
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by assumption();
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by assumption();
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(((remainder_chunk_len as u32) as i32), (((__rust_mir_62_remaining as u32) as i32)))) by assumption();
       have bytes.len() <= 2147483647u64 by assumption();
       have 0 <= ((bytes.len() as u32) as i32) by assumption();
       have 0 <= ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) by assumption();
       have defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)) by assumption();
       have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) <= ((bytes.len() as u32) as i32) by assumption();

       have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64 by assumption();
       have remainder_len == bytes.len() % 4u64 by assumption();
       have __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64;
       have 4u64 <= at(lane_head, __rust_mir_62_remaining) by assumption();
       have __rust_mir_62_remaining <= (bytes.len() - bytes.len() % 4u64) by arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= (bytes.len() - bytes.len() % 4u64); bytes.len() % 4u64 <= bytes.len(); };
       have ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) <= 18446744073709551611u64 by arithmetic() using { 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= (bytes.len() - bytes.len() % 4u64); bytes.len() % 4u64 <= bytes.len(); };
       have at(lane_head, __rust_mir_62_cursor) + 4 == bytes + (((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) + 4u64) by arithmetic() using { at(lane_head, __rust_mir_62_cursor) == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)); ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) <= 18446744073709551611u64; };
       have ((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining) == ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) + 4u64 by arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= (bytes.len() - bytes.len() % 4u64); bytes.len() % 4u64 <= bytes.len(); };
       have __rust_mir_62_cursor == bytes + ((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining) by { rewrite(((bytes.len() - bytes.len() % 4u64) - __rust_mir_62_remaining) == ((bytes.len() - bytes.len() % 4u64) - at(lane_head, __rust_mir_62_remaining)) + 4u64); simp(); }
       have __rust_mir_62_remaining <= 22208u64 by arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= 22208u64; };
       have __rust_mir_62_remaining <= remainder_chunk_len by arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= remainder_chunk_len; };
       apply(adler_bounded_pointer_association(remainder_chunk, (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))))) using { 0 <= ((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) <= 22204; }
       have (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)) == (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) + 4 by arithmetic() using { ((__rust_mir_62_remaining as u32) as i32) == at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4; 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; };
       have __rust_mir_62_cursor == remainder_chunk + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)) by {
        rewrite((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)) == (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) + 4);
        simp() using { __rust_mir_62_cursor == at(lane_head, __rust_mir_62_cursor) + 4; at(lane_head, __rust_mir_62_cursor) == remainder_chunk + (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))); (remainder_chunk + (((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) + 4 == remainder_chunk + ((((remainder_chunk_len as u32) as i32) - at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) + 4); }
       }
       // A advances at the absolute original-input position, using the real iterator state.
       apply(adler_checked_subprefix(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), ((remainder_chunk_len as u32) as i32), ((__rust_mir_62_remaining as u32) as i32))) using { 0 <= ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32); 0 <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 0 <= ((__rust_mir_62_remaining as u32) as i32); ((__rust_mir_62_remaining as u32) as i32) <= ((remainder_chunk_len as u32) as i32); defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)); }
       have (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4 == ((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) by arithmetic() using { 0 <= ((__rust_mir_62_remaining as u32) as i32); ((__rust_mir_62_remaining as u32) as i32) <= ((remainder_chunk_len as u32) as i32); ((remainder_chunk_len as u32) as i32) <= 22204; 0 <= (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4); };
       have defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4)) by { rewrite((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4 == ((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)); assumption(); }
       have defined((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4) by assumption();
       apply(adler_checked_prefix_advance(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32), (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))) using { defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4))); defined((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 4); defined((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4); defined(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4)); }
       have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 4 by { rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 4 == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4)); rewrite((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4 == ((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)); normalize(); }
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))), to_integer(a)) by {
        rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 4);
        rewrite(a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]));
        rewrite(a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]));
        rewrite(a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]));
        rewrite(a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]));
        simp();
       }
       have (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)) == (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4 by { rewrite((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4 == ((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)); normalize(); }
       have 0 <= adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by {
        have to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4) by simp() using { (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)) == (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4; };
        rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4));
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]); };
        rewrite(to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])));
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]); };
        rewrite(to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])));
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]); };
        rewrite(to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])));
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); };
        rewrite(to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))));
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); };
        rewrite(to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))));
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); };
        rewrite(to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))));
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); };
        rewrite(to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))));
        simp();
       }
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))), to_integer(a), old(to_integer((self.b as u32)))) by {
        rewrite((((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4)) + 4);
        have to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4) by simp() using { (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)) == (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4; };
        rewrite(to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32) - 4) + 4));
        have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]); };
        rewrite(to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])));
        have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]); };
        rewrite(to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])));
        have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]); };
        rewrite(to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])));
        have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); };
        rewrite(to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))));
        have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); };
        rewrite(to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))));
        have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); };
        rewrite(to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))));
        have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); };
        rewrite(to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))));
        simp();
       }
       close_invariants by simp();
      }
     }
     have __rust_mir_62_remaining < 4u64 by { cases {
      not (0u64 < __rust_mir_62_remaining) => { have __rust_mir_62_remaining <= 0u64; arithmetic() using { __rust_mir_62_remaining <= 0u64; } }
      not (4u64 <= __rust_mir_62_remaining) => { simp(); }
     } }
     have __rust_mir_62_remaining <= 3u64 by arithmetic() using { __rust_mir_62_remaining < 4u64; };
     have __rust_mir_62_remaining <= 2147483647u64 by arithmetic() using { __rust_mir_62_remaining <= 3u64; };
     apply(adler_bounded_count_upper(__rust_mir_62_remaining, 3));
     have (((__rust_mir_62_remaining as u32) as i32)) < 4 by arithmetic() using { (((__rust_mir_62_remaining as u32) as i32)) <= 3; };

     have (((__rust_mir_62_remaining as u32) as i32)) % 4 == (((__rust_mir_62_remaining as u32) as i32)) by normalize() using { 0 <= (((__rust_mir_62_remaining as u32) as i32)); (((__rust_mir_62_remaining as u32) as i32)) < 4; };
     have (((__rust_mir_62_remaining as u32) as i32)) == 0 by simp() using { (((__rust_mir_62_remaining as u32) as i32)) % 4 == 0; (((__rust_mir_62_remaining as u32) as i32)) % 4 == (((__rust_mir_62_remaining as u32) as i32)); };
     apply(adler_bounded_count(__rust_mir_62_remaining));
     have __rust_mir_62_remaining == 0u64 by simp() using { (((__rust_mir_62_remaining as u32) as i32) as usize) == __rust_mir_62_remaining; (((__rust_mir_62_remaining as u32) as i32)) == 0; };

     have (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32))) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) by { rewrite(((__rust_mir_62_remaining as u32) as i32) == 0); normalize(); }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(a)) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) == (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)))); simp(); }
     apply(adler_complete_remainder_position(((remainder_chunk_len as u32) as i32), ((__rust_mir_62_remaining as u32) as i32))) using { 0 <= ((remainder_chunk_len as u32) as i32); ((__rust_mir_62_remaining as u32) as i32) == 0; }
     have 0 <= adler_lane_b(to_integer(b) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(to_integer(((remainder_chunk_len as u32) as i32)) == to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)))); assumption(); }
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(a), old(to_integer((self.b as u32)))) by { rewrite(((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) == (((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + (((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)))); rewrite(to_integer(((remainder_chunk_len as u32) as i32)) == to_integer((((remainder_chunk_len as u32) as i32) - ((__rust_mir_62_remaining as u32) as i32)))); simp(); }
     mark remainder_lane_prefix;

     have truncating_remainder(adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))), 65521) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32))));
     have 0 <= adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3])));
     have truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))), 65521) == adler_spec_a(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(at(remainder_lane_prefix, a)));
     apply(uint32_to_integer_bounds(at(remainder_lane_prefix, a))) using {};
     apply(uint32_to_integer_bounds(at(remainder_lane_prefix, a_vec.0[0]))) using {};
     apply(uint32_to_integer_bounds(at(remainder_lane_prefix, a_vec.0[1]))) using {};
     apply(uint32_to_integer_bounds(at(remainder_lane_prefix, a_vec.0[2]))) using {};
     apply(uint32_to_integer_bounds(at(remainder_lane_prefix, a_vec.0[3]))) using {};
     apply(adler_lane_a_reduction(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])))) using { 0 <= to_integer(at(remainder_lane_prefix, a)); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[0])); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[1])); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[2])); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[3])); };
     have remainder_len == bytes.len() % 4u64 by assumption();
     execute_until(assignment(__rust_mir_80, 0)); step();
     have __rust_mir_77 == (remainder_chunk_len as u32);
     apply(adler_general_bounded_native_prefix(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_general_native_bounded_prefix_divisible(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_outer_remainder_native_bound(bytes.len() - bytes.len() % 4u64)) using { bytes.len() - bytes.len() % 4u64 <= 2147483644u64; (bytes.len() - bytes.len() % 4u64) % 4u64 == 0u64; }
     have remainder_chunk_len <= 22204u64 by { rewrite(remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64); assumption(); }
     apply(adler_small_length_cast(remainder_chunk_len)) using { remainder_chunk_len <= 22204u64; }
     have __rust_mir_77 <= 22204u32 by { rewrite(__rust_mir_77 == (remainder_chunk_len as u32)); assumption(); }
     have __rust_mir_80 <= 65520u32 by simp() using { a <= 65520u32; };
     apply(adler_scalar_batch_product_bound(__rust_mir_77, __rust_mir_80)) using { __rust_mir_77 <= 22204u32; __rust_mir_80 <= 65520u32; }
     have to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 4294967295 by arithmetic() using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 1454806080; };
     apply(uint32_multiply_guard_by_integer_bound(__rust_mir_77, __rust_mir_80)) using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 4294967295; }
     have remainder_chunk_len <= 22208u64 by arithmetic() using { remainder_chunk_len <= 22204u64; };
     apply(adler_count_observation(remainder_chunk_len)) using { remainder_chunk_len <= 22208u64; };
     apply(adler_remainder_native_count_observation(remainder_chunk_len)) using { remainder_chunk_len <= 22204u64; }
     have to_integer(__rust_mir_77) == to_integer(((remainder_chunk_len as u32) as i32)) by { rewrite(__rust_mir_77 == (remainder_chunk_len as u32)); arithmetic() using { to_integer((remainder_chunk_len as u32)) == to_integer(remainder_chunk_len); to_integer(((remainder_chunk_len as u32) as i32)) == to_integer(remainder_chunk_len); }; }
     mark seed_product;
     have to_integer(at(seed_product, __rust_mir_77)) == to_integer(((remainder_chunk_len as u32) as i32));
     have to_integer(at(seed_product, __rust_mir_80)) == to_integer(at(remainder_lane_prefix, a));
     have to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80)) <= 1454806080 by simp() using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 1454806080; };
     have at(seed_product, __rust_mir_80) == 0u32 or at(seed_product, __rust_mir_77) <= 4294967295u32 / at(seed_product, __rust_mir_80) by simp() using { __rust_mir_80 == 0u32 or __rust_mir_77 <= 4294967295u32 / __rust_mir_80; };
     apply(uint32_multiply_to_integer(at(seed_product, __rust_mir_77), at(seed_product, __rust_mir_80))) using { at(seed_product, __rust_mir_80) == 0u32 or at(seed_product, __rust_mir_77) <= 4294967295u32 / at(seed_product, __rust_mir_80); }
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
     have __rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80);
     have to_integer(__rust_mir_76) == to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)) by { rewrite(__rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)); rewrite(to_integer(at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)) == to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80))); rewrite(to_integer(at(seed_product, __rust_mir_77)) == to_integer(((remainder_chunk_len as u32) as i32))); rewrite(to_integer(at(seed_product, __rust_mir_80)) == to_integer(at(remainder_lane_prefix, a))); simp(); }
     have to_integer(__rust_mir_76) <= 1454806080 by { rewrite(__rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)); rewrite(to_integer(at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)) == to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80))); assumption(); }
     have b <= 65520u32 by assumption();
     apply(uint32_less_equal_to_integer(b, 65520u32)) using { b <= 65520u32; }
     have to_integer(b) + to_integer(__rust_mir_76) <= 4294967295 by arithmetic() using { to_integer(b) <= 65520; to_integer(__rust_mir_76) <= 1454806080; };
     apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_76)) using { to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; }
     mark deferred_b;
     have to_integer(at(deferred_b, b)) == to_integer(at(remainder_lane_prefix, b));
     have to_integer(at(deferred_b, __rust_mir_76)) == to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a));
     have to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)) <= 4294967295 by simp() using { to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; };
     apply(uint32_add_to_integer(at(deferred_b, b), at(deferred_b, __rust_mir_76))) using { to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)) <= 4294967295; };
     execute_until(assignment(__rust_mir_84, 0)); step();
     mark reduction_a;
     have to_integer(at(reduction_a, a_vec.0[0])) == to_integer(at(remainder_lane_prefix, a_vec.0[0]));
     have to_integer(at(reduction_a, a_vec.0[1])) == to_integer(at(remainder_lane_prefix, a_vec.0[1]));
     have to_integer(at(reduction_a, a_vec.0[2])) == to_integer(at(remainder_lane_prefix, a_vec.0[2]));
     have to_integer(at(reduction_a, a_vec.0[3])) == to_integer(at(remainder_lane_prefix, a_vec.0[3]));
     execute_until(assignment(__rust_mir_86, 0)); step();
     mark reduction_b;
     have to_integer(at(reduction_b, b_vec.0[0])) == to_integer(at(remainder_lane_prefix, b_vec.0[0]));
     have to_integer(at(reduction_b, b_vec.0[1])) == to_integer(at(remainder_lane_prefix, b_vec.0[1]));
     have to_integer(at(reduction_b, b_vec.0[2])) == to_integer(at(remainder_lane_prefix, b_vec.0[2]));
     have to_integer(at(reduction_b, b_vec.0[3])) == to_integer(at(remainder_lane_prefix, b_vec.0[3]));
     execute_until(assignment(__rust_mir_88, 0));
     have __rust_checked_77 == at(deferred_b, b) + at(deferred_b, __rust_mir_76);
     have to_integer(__rust_checked_77) == to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)) by simp() using { __rust_checked_77 == at(deferred_b, b) + at(deferred_b, __rust_mir_76); };
     have to_integer(__rust_checked_77) == to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)) by arithmetic() using { to_integer(__rust_checked_77) == to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)); to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)) == to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)); to_integer(at(deferred_b, b)) == to_integer(at(remainder_lane_prefix, b)); to_integer(at(deferred_b, __rust_mir_76)) == to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)); };

     apply(uint32_to_integer_bounds(__rust_checked_77)) using {};
     have 0 <= to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)) by arithmetic() using { 0 <= to_integer(__rust_checked_77); to_integer(__rust_checked_77) == to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)); };
     apply(uint32_to_integer_bounds(at(remainder_lane_prefix, b_vec.0[0]))) using {};
     apply(uint32_to_integer_bounds(at(remainder_lane_prefix, b_vec.0[1]))) using {};
     apply(uint32_to_integer_bounds(at(remainder_lane_prefix, b_vec.0[2]))) using {};
     apply(uint32_to_integer_bounds(at(remainder_lane_prefix, b_vec.0[3]))) using {};
     apply(adler_lane_b_reduction(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3])))) using { 0 <= to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[1])); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[2])); 0 <= to_integer(at(remainder_lane_prefix, a_vec.0[3])); 0 <= to_integer(at(remainder_lane_prefix, b_vec.0[0])); 0 <= to_integer(at(remainder_lane_prefix, b_vec.0[1])); 0 <= to_integer(at(remainder_lane_prefix, b_vec.0[2])); 0 <= to_integer(at(remainder_lane_prefix, b_vec.0[3])); 0 <= adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))); };
     have __rust_checked_82 == 65521u32;
     have 65521u32 == __rust_checked_82 by simp() using { __rust_checked_82 == 65521u32; };
     have b_vec.0[0] < __rust_checked_82;
     have b_vec.0[0] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
     have b_vec.0[0] <= 4294967295u32 / 4u32 by arithmetic() using { b_vec.0[0] < 65521u32; };
     have b_vec.0[1] < __rust_checked_82;
     have b_vec.0[1] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
     have b_vec.0[1] <= 4294967295u32 / 4u32 by arithmetic() using { b_vec.0[1] < 65521u32; };
     have b_vec.0[2] < __rust_checked_82;
     have b_vec.0[2] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
     have b_vec.0[2] <= 4294967295u32 / 4u32 by arithmetic() using { b_vec.0[2] < 65521u32; };
     have b_vec.0[3] < __rust_checked_82;
     have b_vec.0[3] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
     have b_vec.0[3] <= 4294967295u32 / 4u32 by arithmetic() using { b_vec.0[3] < 65521u32; };
     apply(uint32_less_than_to_integer(b_vec.0[0], 65521u32)) using { b_vec.0[0] < 65521u32; }
     have to_integer(b_vec.0[0]) <= 65520 by arithmetic() using { to_integer(b_vec.0[0]) < 65521; };
     apply(uint32_less_than_to_integer(b_vec.0[1], 65521u32)) using { b_vec.0[1] < 65521u32; }
     have to_integer(b_vec.0[1]) <= 65520 by arithmetic() using { to_integer(b_vec.0[1]) < 65521; };
     apply(uint32_less_than_to_integer(b_vec.0[2], 65521u32)) using { b_vec.0[2] < 65521u32; }
     have to_integer(b_vec.0[2]) <= 65520 by arithmetic() using { to_integer(b_vec.0[2]) < 65521; };
     apply(uint32_less_than_to_integer(b_vec.0[3], 65521u32)) using { b_vec.0[3] < 65521u32; }
     have to_integer(b_vec.0[3]) <= 65520 by arithmetic() using { to_integer(b_vec.0[3]) < 65521; };
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a));
     have __rust_checked_84 == 65521u32;
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % __rust_checked_84;
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32 by { rewrite(a_vec.0[0] == at(reduction_a, a_vec.0[0]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
     apply(uint32_remainder_to_integer(at(reduction_a, a_vec.0[0]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(a_vec.0[0]) == to_integer(at(reduction_a, a_vec.0[0]) % 65521u32) by simp() using { a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[0])) == to_integer(at(remainder_lane_prefix, a_vec.0[0]))); simp(); }
     have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521) by arithmetic() using { to_integer(a_vec.0[0]) == to_integer(at(reduction_a, a_vec.0[0]) % 65521u32); to_integer(at(reduction_a, a_vec.0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521); };
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % __rust_checked_84;
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32 by { rewrite(a_vec.0[1] == at(reduction_a, a_vec.0[1]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
     apply(uint32_remainder_to_integer(at(reduction_a, a_vec.0[1]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(a_vec.0[1]) == to_integer(at(reduction_a, a_vec.0[1]) % 65521u32) by simp() using { a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[1])) == to_integer(at(remainder_lane_prefix, a_vec.0[1]))); simp(); }
     have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521) by arithmetic() using { to_integer(a_vec.0[1]) == to_integer(at(reduction_a, a_vec.0[1]) % 65521u32); to_integer(at(reduction_a, a_vec.0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521); };
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % __rust_checked_84;
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32 by { rewrite(a_vec.0[2] == at(reduction_a, a_vec.0[2]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
     apply(uint32_remainder_to_integer(at(reduction_a, a_vec.0[2]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(a_vec.0[2]) == to_integer(at(reduction_a, a_vec.0[2]) % 65521u32) by simp() using { a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[2])) == to_integer(at(remainder_lane_prefix, a_vec.0[2]))); simp(); }
     have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521) by arithmetic() using { to_integer(a_vec.0[2]) == to_integer(at(reduction_a, a_vec.0[2]) % 65521u32); to_integer(at(reduction_a, a_vec.0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521); };
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % __rust_checked_84;
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32 by { rewrite(a_vec.0[3] == at(reduction_a, a_vec.0[3]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
     apply(uint32_remainder_to_integer(at(reduction_a, a_vec.0[3]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(a_vec.0[3]) == to_integer(at(reduction_a, a_vec.0[3]) % 65521u32) by simp() using { a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[3])) == to_integer(at(remainder_lane_prefix, a_vec.0[3]))); simp(); }
     have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521) by arithmetic() using { to_integer(a_vec.0[3]) == to_integer(at(reduction_a, a_vec.0[3]) % 65521u32); to_integer(at(reduction_a, a_vec.0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521); };
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(at(remainder_lane_prefix, a))) by { rewrite(to_integer(a) == to_integer(at(remainder_lane_prefix, a))); rewrite(to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521)); rewrite(to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521)); rewrite(to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521)); rewrite(to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521)); arithmetic() using { truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))), 65521) == truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[0])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521)), 65521); truncating_remainder(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[0])), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3]))), 65521) == adler_spec_a(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(at(remainder_lane_prefix, a))); } }
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % __rust_checked_82;
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32 by { rewrite(b_vec.0[0] == at(reduction_b, b_vec.0[0]) % __rust_checked_82); simp() using { __rust_checked_82 == 65521u32; } }
     apply(uint32_remainder_to_integer(at(reduction_b, b_vec.0[0]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(b_vec.0[0]) == to_integer(at(reduction_b, b_vec.0[0]) % 65521u32) by simp() using { b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[0])) == to_integer(at(remainder_lane_prefix, b_vec.0[0]))); simp(); }
     have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521) by arithmetic() using { to_integer(b_vec.0[0]) == to_integer(at(reduction_b, b_vec.0[0]) % 65521u32); to_integer(at(reduction_b, b_vec.0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521); };
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % __rust_checked_82;
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32 by { rewrite(b_vec.0[1] == at(reduction_b, b_vec.0[1]) % __rust_checked_82); simp() using { __rust_checked_82 == 65521u32; } }
     apply(uint32_remainder_to_integer(at(reduction_b, b_vec.0[1]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(b_vec.0[1]) == to_integer(at(reduction_b, b_vec.0[1]) % 65521u32) by simp() using { b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[1])) == to_integer(at(remainder_lane_prefix, b_vec.0[1]))); simp(); }
     have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521) by arithmetic() using { to_integer(b_vec.0[1]) == to_integer(at(reduction_b, b_vec.0[1]) % 65521u32); to_integer(at(reduction_b, b_vec.0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521); };
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % __rust_checked_82;
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32 by { rewrite(b_vec.0[2] == at(reduction_b, b_vec.0[2]) % __rust_checked_82); simp() using { __rust_checked_82 == 65521u32; } }
     apply(uint32_remainder_to_integer(at(reduction_b, b_vec.0[2]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(b_vec.0[2]) == to_integer(at(reduction_b, b_vec.0[2]) % 65521u32) by simp() using { b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[2])) == to_integer(at(remainder_lane_prefix, b_vec.0[2]))); simp(); }
     have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521) by arithmetic() using { to_integer(b_vec.0[2]) == to_integer(at(reduction_b, b_vec.0[2]) % 65521u32); to_integer(at(reduction_b, b_vec.0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521); };
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % __rust_checked_82;
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32 by { rewrite(b_vec.0[3] == at(reduction_b, b_vec.0[3]) % __rust_checked_82); simp() using { __rust_checked_82 == 65521u32; } }
     apply(uint32_remainder_to_integer(at(reduction_b, b_vec.0[3]), 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(b_vec.0[3]) == to_integer(at(reduction_b, b_vec.0[3]) % 65521u32) by simp() using { b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[3])) == to_integer(at(remainder_lane_prefix, b_vec.0[3]))); simp(); }
     have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521) by arithmetic() using { to_integer(b_vec.0[3]) == to_integer(at(reduction_b, b_vec.0[3]) % 65521u32); to_integer(at(reduction_b, b_vec.0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521); };
     have __rust_checked_79 == 65521u32;
     have b == __rust_checked_77 % __rust_checked_79;
     have b == __rust_checked_77 % 65521u32 by { rewrite(b == __rust_checked_77 % __rust_checked_79); simp() using { __rust_checked_79 == 65521u32; } }
     apply(uint32_remainder_to_integer(__rust_checked_77, 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(b) == to_integer(__rust_checked_77 % 65521u32) by simp() using { b == __rust_checked_77 % 65521u32; };
     have truncating_remainder(to_integer(__rust_checked_77), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521) by { rewrite(to_integer(__rust_checked_77) == to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a))); simp(); }
     have to_integer(b) == truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521) by arithmetic() using { to_integer(b) == to_integer(__rust_checked_77 % 65521u32); to_integer(__rust_checked_77 % 65521u32) == truncating_remainder(to_integer(__rust_checked_77), to_integer(65521u32)); truncating_remainder(to_integer(__rust_checked_77), 65521) == truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521); };
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b) == truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521)); rewrite(to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521)); rewrite(to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521)); rewrite(to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521)); rewrite(to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521)); rewrite(to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521)); rewrite(to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521)); rewrite(to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521)); arithmetic() using { truncating_remainder(adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))), 65521) == truncating_remainder(adler_lane_b(truncating_remainder(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, a_vec.0[3])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[0])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[1])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[2])), 65521), truncating_remainder(to_integer(at(remainder_lane_prefix, b_vec.0[3])), 65521)), 65521); truncating_remainder(adler_lane_b(to_integer(at(remainder_lane_prefix, b)) + to_integer(((remainder_chunk_len as u32) as i32)) * to_integer(at(remainder_lane_prefix, a)), to_integer(at(remainder_lane_prefix, a_vec.0[1])), to_integer(at(remainder_lane_prefix, a_vec.0[2])), to_integer(at(remainder_lane_prefix, a_vec.0[3])), to_integer(at(remainder_lane_prefix, b_vec.0[0])), to_integer(at(remainder_lane_prefix, b_vec.0[1])), to_integer(at(remainder_lane_prefix, b_vec.0[2])), to_integer(at(remainder_lane_prefix, b_vec.0[3]))), 65521) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32)))); } }
     mark weighted_b;
     have truncating_remainder(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))), 65521) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32))));
     execute_until(assignment(__rust_mir_91, 0));
     have __rust_checked_85 == 65521u32;
     have 65521u32 == __rust_checked_85 by simp() using { __rust_checked_85 == 65521u32; };
     have a_vec.0[0] < __rust_checked_85;
     have a_vec.0[0] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
     have a_vec.0[1] < __rust_checked_85;
     have a_vec.0[1] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
     have a_vec.0[2] < __rust_checked_85;
     have a_vec.0[2] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
     have a_vec.0[3] < __rust_checked_85;
     have a_vec.0[3] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have to_integer(at(weighted_b, b_vec.0[0])) <= 65520;
     have to_integer(b_vec.0[0]) <= 262080 by arithmetic() using { to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4; to_integer(at(weighted_b, b_vec.0[0])) <= 65520; };
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(at(weighted_b, b_vec.0[1])) <= 65520;
     have to_integer(b_vec.0[1]) <= 262080 by arithmetic() using { to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4; to_integer(at(weighted_b, b_vec.0[1])) <= 65520; };
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(at(weighted_b, b_vec.0[2])) <= 65520;
     have to_integer(b_vec.0[2]) <= 262080 by arithmetic() using { to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4; to_integer(at(weighted_b, b_vec.0[2])) <= 65520; };
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(at(weighted_b, b_vec.0[3])) <= 65520;
     have to_integer(b_vec.0[3]) <= 262080 by arithmetic() using { to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4; to_integer(at(weighted_b, b_vec.0[3])) <= 65520; };
     mark correction_b;
     have to_integer(at(correction_b, b_vec.0[1])) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(at(correction_b, a_vec.0[1])) == to_integer(at(weighted_b, a_vec.0[1]));
     have to_integer(at(correction_b, b_vec.0[2])) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(at(correction_b, a_vec.0[2])) == to_integer(at(weighted_b, a_vec.0[2]));
     have to_integer(at(correction_b, b_vec.0[3])) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(at(correction_b, a_vec.0[3])) == to_integer(at(weighted_b, a_vec.0[3]));
     apply(adler_recombine_lane_1(a_vec.0[1], b_vec.0[1])) using { a_vec.0[1] < 65521u32; to_integer(b_vec.0[1]) <= 262080; }
     apply(adler_recombine_lane_2(a_vec.0[2], b_vec.0[2])) using { a_vec.0[2] < 65521u32; to_integer(b_vec.0[2]) <= 262080; }
     apply(adler_recombine_lane_3(a_vec.0[3], b_vec.0[3])) using { a_vec.0[3] < 65521u32; to_integer(b_vec.0[3]) <= 262080; }
     apply(adler_recombine_difference(a_vec.0[2])) using { a_vec.0[2] < 65521u32; }
     have 65521u32 - a_vec.0[2] <= 4294967295u32 / 2u32 by arithmetic() using { 65521u32 - a_vec.0[2] <= 65521u32; };
     apply(adler_recombine_difference(a_vec.0[3])) using { a_vec.0[3] < 65521u32; }
     have 65521u32 - a_vec.0[3] <= 4294967295u32 / 3u32 by arithmetic() using { 65521u32 - a_vec.0[3] <= 65521u32; };
     have to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) == to_integer(at(correction_b, b_vec.0[1])) + (65521 - to_integer(at(correction_b, a_vec.0[1]))) * 1;
     have to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) == to_integer(at(correction_b, b_vec.0[2])) + (65521 - to_integer(at(correction_b, a_vec.0[2]))) * 2;
     have to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) == to_integer(at(correction_b, b_vec.0[3])) + (65521 - to_integer(at(correction_b, a_vec.0[3]))) * 3;
     execute_until(assignment(__rust_mir_94, 0));
     have __rust_mir_89 == (65521u32 - at(correction_b, a_vec.0[1]));
     have b_vec.0[1] == at(correction_b, b_vec.0[1]);
     mark correction_add_1;
     have at(correction_add_1, __rust_mir_89) == (65521u32 - at(correction_b, a_vec.0[1]));
     have at(correction_add_1, b_vec.0[1]) == at(correction_b, b_vec.0[1]);
     step();
     have __rust_mir_94 == at(correction_add_1, b_vec.0[1]) + at(correction_add_1, __rust_mir_89);
     have __rust_mir_94 == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1])) by { rewrite(__rust_mir_94 == at(correction_add_1, b_vec.0[1]) + at(correction_add_1, __rust_mir_89)); rewrite(at(correction_add_1, b_vec.0[1]) == at(correction_b, b_vec.0[1])); rewrite(at(correction_add_1, __rust_mir_89) == (65521u32 - at(correction_b, a_vec.0[1]))); simp(); }
     mark correction_store_1;
     have at(correction_store_1, __rust_mir_94) == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]));
     execute_until(assignment(__rust_mir_102, 0));
     have __rust_mir_95 == ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32);
     have b_vec.0[2] == at(correction_b, b_vec.0[2]);
     mark correction_add_2;
     have at(correction_add_2, __rust_mir_95) == ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32);
     have at(correction_add_2, b_vec.0[2]) == at(correction_b, b_vec.0[2]);
     step();
     have __rust_mir_102 == at(correction_add_2, b_vec.0[2]) + at(correction_add_2, __rust_mir_95);
     have __rust_mir_102 == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32) by { rewrite(__rust_mir_102 == at(correction_add_2, b_vec.0[2]) + at(correction_add_2, __rust_mir_95)); rewrite(at(correction_add_2, b_vec.0[2]) == at(correction_b, b_vec.0[2])); rewrite(at(correction_add_2, __rust_mir_95) == ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)); simp(); }
     mark correction_store_2;
     have at(correction_store_2, __rust_mir_102) == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32);
     execute_until(assignment(__rust_mir_104, 0)); step();
     have __rust_mir_104 == 65521u32 - at(correction_b, a_vec.0[3]);
     execute_until(assignment(__rust_mir_108, 0));
     mark correction_multiply_3;
     have at(correction_multiply_3, __rust_mir_104) == 65521u32 - at(correction_b, a_vec.0[3]);
     step();
     have __rust_mir_108 == at(correction_multiply_3, __rust_mir_104) * 3u32;
     have __rust_mir_108 == (65521u32 - at(correction_b, a_vec.0[3])) * 3u32 by { rewrite(__rust_mir_108 == at(correction_multiply_3, __rust_mir_104) * 3u32); rewrite(at(correction_multiply_3, __rust_mir_104) == 65521u32 - at(correction_b, a_vec.0[3])); simp(); }
     execute_until(assignment(__rust_mir_103, 0)); step();
     have __rust_mir_103 == (65521u32 - at(correction_b, a_vec.0[3])) * 3u32 by simp() using { __rust_mir_108 == (65521u32 - at(correction_b, a_vec.0[3])) * 3u32; };
     execute_until(assignment(__rust_mir_110, 0));
     have b_vec.0[3] == at(correction_b, b_vec.0[3]);
     mark correction_add_3;
     have at(correction_add_3, __rust_mir_103) == ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32);
     have at(correction_add_3, b_vec.0[3]) == at(correction_b, b_vec.0[3]);
     step();
     have __rust_mir_110 == at(correction_add_3, b_vec.0[3]) + at(correction_add_3, __rust_mir_103);
     have __rust_mir_110 == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32) by { rewrite(__rust_mir_110 == at(correction_add_3, b_vec.0[3]) + at(correction_add_3, __rust_mir_103)); rewrite(at(correction_add_3, b_vec.0[3]) == at(correction_b, b_vec.0[3])); rewrite(at(correction_add_3, __rust_mir_103) == ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)); simp(); }
     mark correction_store_3;
     have at(correction_store_3, __rust_mir_110) == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32);
     execute_until(loop(3));
     have b_vec.0[1] == at(correction_store_1, __rust_mir_94);
     have b_vec.0[1] == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1])) by { rewrite(b_vec.0[1] == at(correction_store_1, __rust_mir_94)); rewrite(at(correction_store_1, __rust_mir_94) == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))); simp(); }
     have to_integer(b_vec.0[1]) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) by simp() using { b_vec.0[1] == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1])); };
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[1]))) * 1 by arithmetic() using { to_integer(b_vec.0[1]) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))); to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) == to_integer(at(correction_b, b_vec.0[1])) + (65521 - to_integer(at(correction_b, a_vec.0[1]))) * 1; to_integer(at(correction_b, b_vec.0[1])) == to_integer(at(weighted_b, b_vec.0[1])) * 4; to_integer(at(correction_b, a_vec.0[1])) == to_integer(at(weighted_b, a_vec.0[1])); };
     have b_vec.0[2] == at(correction_store_2, __rust_mir_102);
     have b_vec.0[2] == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32) by { rewrite(b_vec.0[2] == at(correction_store_2, __rust_mir_102)); rewrite(at(correction_store_2, __rust_mir_102) == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)); simp(); }
     have to_integer(b_vec.0[2]) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) by simp() using { b_vec.0[2] == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32); };
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[2]))) * 2 by arithmetic() using { to_integer(b_vec.0[2]) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)); to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) == to_integer(at(correction_b, b_vec.0[2])) + (65521 - to_integer(at(correction_b, a_vec.0[2]))) * 2; to_integer(at(correction_b, b_vec.0[2])) == to_integer(at(weighted_b, b_vec.0[2])) * 4; to_integer(at(correction_b, a_vec.0[2])) == to_integer(at(weighted_b, a_vec.0[2])); };
     have b_vec.0[3] == at(correction_store_3, __rust_mir_110);
     have b_vec.0[3] == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32) by { rewrite(b_vec.0[3] == at(correction_store_3, __rust_mir_110)); rewrite(at(correction_store_3, __rust_mir_110) == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)); simp(); }
     have to_integer(b_vec.0[3]) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) by simp() using { b_vec.0[3] == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32); };
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[3]))) * 3 by arithmetic() using { to_integer(b_vec.0[3]) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)); to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) == to_integer(at(correction_b, b_vec.0[3])) + (65521 - to_integer(at(correction_b, a_vec.0[3]))) * 3; to_integer(at(correction_b, b_vec.0[3])) == to_integer(at(weighted_b, b_vec.0[3])) * 4; to_integer(at(correction_b, a_vec.0[3])) == to_integer(at(weighted_b, a_vec.0[3])); };
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have a <= 65520u32 by assumption();
     apply(uint32_less_equal_to_integer(a, 65520u32)) using { a <= 65520u32; }
     execute_until(assignment(__rust_mir_121, 0));
     have av == a_vec.0[0];
     apply(uint32_less_than_to_integer(a_vec.0[0], 65521u32)) using { a_vec.0[0] < 65521u32; }
     have to_integer(av) <= 65520 by { rewrite(av == a_vec.0[0]); arithmetic() using { to_integer(a_vec.0[0]) < 65521; } }
     step();
     have to_integer(__rust_mir_121) <= 65520 by simp() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by arithmetic() using { to_integer(a) <= 65520; to_integer(__rust_mir_121) <= 65520; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
     execute_until(assignment(__rust_mir_122, 0));
     mark remainder_sum_a_0;
     have to_integer(at(remainder_sum_a_0, a)) == to_integer(at(remainder_lane_prefix, a));
     have to_integer(at(remainder_sum_a_0, __rust_mir_121)) == to_integer(a_vec.0[0]);
     have to_integer(at(remainder_sum_a_0, a)) <= 65520 by simp() using { to_integer(a) <= 65520; };
     have to_integer(at(remainder_sum_a_0, __rust_mir_121)) <= 65520 by simp() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)) <= 4294967295 by arithmetic() using { to_integer(at(remainder_sum_a_0, a)) <= 65520; to_integer(at(remainder_sum_a_0, __rust_mir_121)) <= 65520; };
     step();
     have __rust_mir_122 == at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121);
     apply(uint32_add_to_integer(at(remainder_sum_a_0, a), at(remainder_sum_a_0, __rust_mir_121))) using { to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)) <= 4294967295; }
     have to_integer(__rust_mir_122) <= 131040 by { rewrite(__rust_mir_122 == at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121)); rewrite(to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121)) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121))); arithmetic() using { to_integer(at(remainder_sum_a_0, a)) <= 65520; to_integer(at(remainder_sum_a_0, __rust_mir_121)) <= 65520; } }
     execute_until(assignment(a, 1)); step();
     have to_integer(a) <= 131040 by simp() using { to_integer(__rust_mir_122) <= 131040; };
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)) by simp() using { __rust_mir_122 == at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121); to_integer(at(remainder_sum_a_0, a) + at(remainder_sum_a_0, __rust_mir_121)) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) by arithmetic() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_0, a)) + to_integer(at(remainder_sum_a_0, __rust_mir_121)); to_integer(at(remainder_sum_a_0, a)) == to_integer(at(remainder_lane_prefix, a)); to_integer(at(remainder_sum_a_0, __rust_mir_121)) == to_integer(a_vec.0[0]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     execute_until(assignment(__rust_mir_121, 0));
     have av == a_vec.0[1];
     apply(uint32_less_than_to_integer(a_vec.0[1], 65521u32)) using { a_vec.0[1] < 65521u32; }
     have to_integer(av) <= 65520 by { rewrite(av == a_vec.0[1]); arithmetic() using { to_integer(a_vec.0[1]) < 65521; } }
     step();
     have to_integer(__rust_mir_121) <= 65520 by simp() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by arithmetic() using { to_integer(a) <= 131040; to_integer(__rust_mir_121) <= 65520; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
     execute_until(assignment(__rust_mir_122, 0));
     mark remainder_sum_a_1;
     have to_integer(at(remainder_sum_a_1, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]);
     have to_integer(at(remainder_sum_a_1, __rust_mir_121)) == to_integer(a_vec.0[1]);
     have to_integer(at(remainder_sum_a_1, a)) <= 131040 by simp() using { to_integer(a) <= 131040; };
     have to_integer(at(remainder_sum_a_1, __rust_mir_121)) <= 65520 by simp() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)) <= 4294967295 by arithmetic() using { to_integer(at(remainder_sum_a_1, a)) <= 131040; to_integer(at(remainder_sum_a_1, __rust_mir_121)) <= 65520; };
     step();
     have __rust_mir_122 == at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121);
     apply(uint32_add_to_integer(at(remainder_sum_a_1, a), at(remainder_sum_a_1, __rust_mir_121))) using { to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)) <= 4294967295; }
     have to_integer(__rust_mir_122) <= 196560 by { rewrite(__rust_mir_122 == at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121)); rewrite(to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121)) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121))); arithmetic() using { to_integer(at(remainder_sum_a_1, a)) <= 131040; to_integer(at(remainder_sum_a_1, __rust_mir_121)) <= 65520; } }
     execute_until(assignment(a, 1)); step();
     have to_integer(a) <= 196560 by simp() using { to_integer(__rust_mir_122) <= 196560; };
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)) by simp() using { __rust_mir_122 == at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121); to_integer(at(remainder_sum_a_1, a) + at(remainder_sum_a_1, __rust_mir_121)) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) by arithmetic() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_1, a)) + to_integer(at(remainder_sum_a_1, __rust_mir_121)); to_integer(at(remainder_sum_a_1, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]); to_integer(at(remainder_sum_a_1, __rust_mir_121)) == to_integer(a_vec.0[1]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     execute_until(assignment(__rust_mir_121, 0));
     have av == a_vec.0[2];
     apply(uint32_less_than_to_integer(a_vec.0[2], 65521u32)) using { a_vec.0[2] < 65521u32; }
     have to_integer(av) <= 65520 by { rewrite(av == a_vec.0[2]); arithmetic() using { to_integer(a_vec.0[2]) < 65521; } }
     step();
     have to_integer(__rust_mir_121) <= 65520 by simp() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by arithmetic() using { to_integer(a) <= 196560; to_integer(__rust_mir_121) <= 65520; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
     execute_until(assignment(__rust_mir_122, 0));
     mark remainder_sum_a_2;
     have to_integer(at(remainder_sum_a_2, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]);
     have to_integer(at(remainder_sum_a_2, __rust_mir_121)) == to_integer(a_vec.0[2]);
     have to_integer(at(remainder_sum_a_2, a)) <= 196560 by simp() using { to_integer(a) <= 196560; };
     have to_integer(at(remainder_sum_a_2, __rust_mir_121)) <= 65520 by simp() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)) <= 4294967295 by arithmetic() using { to_integer(at(remainder_sum_a_2, a)) <= 196560; to_integer(at(remainder_sum_a_2, __rust_mir_121)) <= 65520; };
     step();
     have __rust_mir_122 == at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121);
     apply(uint32_add_to_integer(at(remainder_sum_a_2, a), at(remainder_sum_a_2, __rust_mir_121))) using { to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)) <= 4294967295; }
     have to_integer(__rust_mir_122) <= 262080 by { rewrite(__rust_mir_122 == at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121)); rewrite(to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121)) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121))); arithmetic() using { to_integer(at(remainder_sum_a_2, a)) <= 196560; to_integer(at(remainder_sum_a_2, __rust_mir_121)) <= 65520; } }
     execute_until(assignment(a, 1)); step();
     have to_integer(a) <= 262080 by simp() using { to_integer(__rust_mir_122) <= 262080; };
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)) by simp() using { __rust_mir_122 == at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121); to_integer(at(remainder_sum_a_2, a) + at(remainder_sum_a_2, __rust_mir_121)) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) by arithmetic() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_2, a)) + to_integer(at(remainder_sum_a_2, __rust_mir_121)); to_integer(at(remainder_sum_a_2, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]); to_integer(at(remainder_sum_a_2, __rust_mir_121)) == to_integer(a_vec.0[2]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     execute_until(assignment(__rust_mir_121, 0));
     have av == a_vec.0[3];
     apply(uint32_less_than_to_integer(a_vec.0[3], 65521u32)) using { a_vec.0[3] < 65521u32; }
     have to_integer(av) <= 65520 by { rewrite(av == a_vec.0[3]); arithmetic() using { to_integer(a_vec.0[3]) < 65521; } }
     step();
     have to_integer(__rust_mir_121) <= 65520 by simp() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by arithmetic() using { to_integer(a) <= 262080; to_integer(__rust_mir_121) <= 65520; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
     execute_until(assignment(__rust_mir_122, 0));
     mark remainder_sum_a_3;
     have to_integer(at(remainder_sum_a_3, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]);
     have to_integer(at(remainder_sum_a_3, __rust_mir_121)) == to_integer(a_vec.0[3]);
     have to_integer(at(remainder_sum_a_3, a)) <= 262080 by simp() using { to_integer(a) <= 262080; };
     have to_integer(at(remainder_sum_a_3, __rust_mir_121)) <= 65520 by simp() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)) <= 4294967295 by arithmetic() using { to_integer(at(remainder_sum_a_3, a)) <= 262080; to_integer(at(remainder_sum_a_3, __rust_mir_121)) <= 65520; };
     step();
     have __rust_mir_122 == at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121);
     apply(uint32_add_to_integer(at(remainder_sum_a_3, a), at(remainder_sum_a_3, __rust_mir_121))) using { to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)) <= 4294967295; }
     have to_integer(__rust_mir_122) <= 327600 by { rewrite(__rust_mir_122 == at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121)); rewrite(to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121)) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121))); arithmetic() using { to_integer(at(remainder_sum_a_3, a)) <= 262080; to_integer(at(remainder_sum_a_3, __rust_mir_121)) <= 65520; } }
     execute_until(assignment(a, 1)); step();
     have to_integer(a) <= 327600 by simp() using { to_integer(__rust_mir_122) <= 327600; };
     have to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)) by simp() using { __rust_mir_122 == at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121); to_integer(at(remainder_sum_a_3, a) + at(remainder_sum_a_3, __rust_mir_121)) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) + to_integer(a_vec.0[3]) by arithmetic() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(remainder_sum_a_3, a)) + to_integer(at(remainder_sum_a_3, __rust_mir_121)); to_integer(at(remainder_sum_a_3, a)) == to_integer(at(remainder_lane_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]); to_integer(at(remainder_sum_a_3, __rust_mir_121)) == to_integer(a_vec.0[3]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(a) == adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) by { unfold(adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); assumption(); }
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(at(remainder_lane_prefix, a))) by { rewrite(to_integer(a) == adler_lane_a(to_integer(at(remainder_lane_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); assumption(); }
     execute_until(loop(4));
     have __rust_checked_79 == 65521u32;
     have 65521u32 == __rust_checked_79 by simp() using { __rust_checked_79 == 65521u32; };
     have b == __rust_checked_77 % __rust_checked_79;
     have __rust_checked_79 != 0u32 by { rewrite(__rust_checked_79 == 65521u32); normalize(); }
     apply(uint32_remainder_less_than_divisor(__rust_checked_77, __rust_checked_79)) using { __rust_checked_79 != 0u32; }
     have b < __rust_checked_79 by { rewrite(b == __rust_checked_77 % __rust_checked_79); assumption(); }
     have b < 65521u32 by { rewrite(65521u32 == __rust_checked_79); assumption(); }
     apply(uint32_less_than_to_integer(b, 65521u32)) using { b < 65521u32; }
     have to_integer(b) <= 65520 by arithmetic() using { to_integer(b) < 65521; };
     have to_integer(b_vec.0[0]) <= 262080;
     execute_until(assignment(__rust_mir_133, 0));
     have bv == b_vec.0[0];
     have to_integer(bv) <= 262080 by { rewrite(bv == b_vec.0[0]); assumption(); }
     step();
     have to_integer(__rust_mir_133) <= 262080 by simp() using { to_integer(bv) <= 262080; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by arithmetic() using { to_integer(b) <= 65520; to_integer(__rust_mir_133) <= 262080; };
     apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
     execute_until(assignment(__rust_mir_134, 0));
     mark remainder_sum_b_0;
     have to_integer(at(remainder_sum_b_0, b)) == to_integer(at(weighted_b, b));
     have to_integer(at(remainder_sum_b_0, __rust_mir_133)) == to_integer(b_vec.0[0]);
     have to_integer(at(remainder_sum_b_0, b)) <= 65520 by simp() using { to_integer(b) <= 65520; };
     have to_integer(at(remainder_sum_b_0, __rust_mir_133)) <= 262080 by simp() using { to_integer(__rust_mir_133) <= 262080; };
     have to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)) <= 4294967295 by arithmetic() using { to_integer(at(remainder_sum_b_0, b)) <= 65520; to_integer(at(remainder_sum_b_0, __rust_mir_133)) <= 262080; };
     step();
     have __rust_mir_134 == at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133);
     apply(uint32_add_to_integer(at(remainder_sum_b_0, b), at(remainder_sum_b_0, __rust_mir_133))) using { to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)) <= 4294967295; }
     have to_integer(__rust_mir_134) <= 327600 by { rewrite(__rust_mir_134 == at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133)); rewrite(to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133)) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133))); arithmetic() using { to_integer(at(remainder_sum_b_0, b)) <= 65520; to_integer(at(remainder_sum_b_0, __rust_mir_133)) <= 262080; } }
     execute_until(assignment(b, 5)); step();
     have to_integer(b) <= 327600 by simp() using { to_integer(__rust_mir_134) <= 327600; };
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)) by simp() using { __rust_mir_134 == at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133); to_integer(at(remainder_sum_b_0, b) + at(remainder_sum_b_0, __rust_mir_133)) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) by arithmetic() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_0, b)) + to_integer(at(remainder_sum_b_0, __rust_mir_133)); to_integer(at(remainder_sum_b_0, b)) == to_integer(at(weighted_b, b)); to_integer(at(remainder_sum_b_0, __rust_mir_133)) == to_integer(b_vec.0[0]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(b_vec.0[1]) <= 327601;
     execute_until(assignment(__rust_mir_133, 0));
     have bv == b_vec.0[1];
     have to_integer(bv) <= 327601 by { rewrite(bv == b_vec.0[1]); assumption(); }
     step();
     have to_integer(__rust_mir_133) <= 327601 by simp() using { to_integer(bv) <= 327601; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by arithmetic() using { to_integer(b) <= 327600; to_integer(__rust_mir_133) <= 327601; };
     apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
     execute_until(assignment(__rust_mir_134, 0));
     mark remainder_sum_b_1;
     have to_integer(at(remainder_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]);
     have to_integer(at(remainder_sum_b_1, __rust_mir_133)) == to_integer(b_vec.0[1]);
     have to_integer(at(remainder_sum_b_1, b)) <= 327600 by simp() using { to_integer(b) <= 327600; };
     have to_integer(at(remainder_sum_b_1, __rust_mir_133)) <= 327601 by simp() using { to_integer(__rust_mir_133) <= 327601; };
     have to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)) <= 4294967295 by arithmetic() using { to_integer(at(remainder_sum_b_1, b)) <= 327600; to_integer(at(remainder_sum_b_1, __rust_mir_133)) <= 327601; };
     step();
     have __rust_mir_134 == at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133);
     apply(uint32_add_to_integer(at(remainder_sum_b_1, b), at(remainder_sum_b_1, __rust_mir_133))) using { to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)) <= 4294967295; }
     have to_integer(__rust_mir_134) <= 655201 by { rewrite(__rust_mir_134 == at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133)); rewrite(to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133)) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133))); arithmetic() using { to_integer(at(remainder_sum_b_1, b)) <= 327600; to_integer(at(remainder_sum_b_1, __rust_mir_133)) <= 327601; } }
     execute_until(assignment(b, 5)); step();
     have to_integer(b) <= 655201 by simp() using { to_integer(__rust_mir_134) <= 655201; };
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)) by simp() using { __rust_mir_134 == at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133); to_integer(at(remainder_sum_b_1, b) + at(remainder_sum_b_1, __rust_mir_133)) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) by arithmetic() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_1, b)) + to_integer(at(remainder_sum_b_1, __rust_mir_133)); to_integer(at(remainder_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]); to_integer(at(remainder_sum_b_1, __rust_mir_133)) == to_integer(b_vec.0[1]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(b_vec.0[2]) <= 393122;
     execute_until(assignment(__rust_mir_133, 0));
     have bv == b_vec.0[2];
     have to_integer(bv) <= 393122 by { rewrite(bv == b_vec.0[2]); assumption(); }
     step();
     have to_integer(__rust_mir_133) <= 393122 by simp() using { to_integer(bv) <= 393122; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by arithmetic() using { to_integer(b) <= 655201; to_integer(__rust_mir_133) <= 393122; };
     apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
     execute_until(assignment(__rust_mir_134, 0));
     mark remainder_sum_b_2;
     have to_integer(at(remainder_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]);
     have to_integer(at(remainder_sum_b_2, __rust_mir_133)) == to_integer(b_vec.0[2]);
     have to_integer(at(remainder_sum_b_2, b)) <= 655201 by simp() using { to_integer(b) <= 655201; };
     have to_integer(at(remainder_sum_b_2, __rust_mir_133)) <= 393122 by simp() using { to_integer(__rust_mir_133) <= 393122; };
     have to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)) <= 4294967295 by arithmetic() using { to_integer(at(remainder_sum_b_2, b)) <= 655201; to_integer(at(remainder_sum_b_2, __rust_mir_133)) <= 393122; };
     step();
     have __rust_mir_134 == at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133);
     apply(uint32_add_to_integer(at(remainder_sum_b_2, b), at(remainder_sum_b_2, __rust_mir_133))) using { to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)) <= 4294967295; }
     have to_integer(__rust_mir_134) <= 1048323 by { rewrite(__rust_mir_134 == at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133)); rewrite(to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133)) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133))); arithmetic() using { to_integer(at(remainder_sum_b_2, b)) <= 655201; to_integer(at(remainder_sum_b_2, __rust_mir_133)) <= 393122; } }
     execute_until(assignment(b, 5)); step();
     have to_integer(b) <= 1048323 by simp() using { to_integer(__rust_mir_134) <= 1048323; };
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)) by simp() using { __rust_mir_134 == at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133); to_integer(at(remainder_sum_b_2, b) + at(remainder_sum_b_2, __rust_mir_133)) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) by arithmetic() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_2, b)) + to_integer(at(remainder_sum_b_2, __rust_mir_133)); to_integer(at(remainder_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]); to_integer(at(remainder_sum_b_2, __rust_mir_133)) == to_integer(b_vec.0[2]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(b_vec.0[3]) <= 458643;
     execute_until(assignment(__rust_mir_133, 0));
     have bv == b_vec.0[3];
     have to_integer(bv) <= 458643 by { rewrite(bv == b_vec.0[3]); assumption(); }
     step();
     have to_integer(__rust_mir_133) <= 458643 by simp() using { to_integer(bv) <= 458643; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by arithmetic() using { to_integer(b) <= 1048323; to_integer(__rust_mir_133) <= 458643; };
     apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
     execute_until(assignment(__rust_mir_134, 0));
     mark remainder_sum_b_3;
     have to_integer(at(remainder_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]);
     have to_integer(at(remainder_sum_b_3, __rust_mir_133)) == to_integer(b_vec.0[3]);
     have to_integer(at(remainder_sum_b_3, b)) <= 1048323 by simp() using { to_integer(b) <= 1048323; };
     have to_integer(at(remainder_sum_b_3, __rust_mir_133)) <= 458643 by simp() using { to_integer(__rust_mir_133) <= 458643; };
     have to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)) <= 4294967295 by arithmetic() using { to_integer(at(remainder_sum_b_3, b)) <= 1048323; to_integer(at(remainder_sum_b_3, __rust_mir_133)) <= 458643; };
     step();
     have __rust_mir_134 == at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133);
     apply(uint32_add_to_integer(at(remainder_sum_b_3, b), at(remainder_sum_b_3, __rust_mir_133))) using { to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)) <= 4294967295; }
     have to_integer(__rust_mir_134) <= 1506966 by { rewrite(__rust_mir_134 == at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133)); rewrite(to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133)) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133))); arithmetic() using { to_integer(at(remainder_sum_b_3, b)) <= 1048323; to_integer(at(remainder_sum_b_3, __rust_mir_133)) <= 458643; } }
     execute_until(assignment(b, 5)); step();
     have to_integer(b) <= 1506966 by simp() using { to_integer(__rust_mir_134) <= 1506966; };
     have to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)) by simp() using { __rust_mir_134 == at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133); to_integer(at(remainder_sum_b_3, b) + at(remainder_sum_b_3, __rust_mir_133)) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) + to_integer(b_vec.0[3]) by arithmetic() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(remainder_sum_b_3, b)) + to_integer(at(remainder_sum_b_3, __rust_mir_133)); to_integer(at(remainder_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]); to_integer(at(remainder_sum_b_3, __rust_mir_133)) == to_integer(b_vec.0[3]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have remainder_len == bytes.len() % 4u64 by assumption();
     apply(adler_general_bounded_tail_metadata(bytes.len())) using { bytes.len() <= 2147483647u64; }
     have remainder_len <= 3u64 by { rewrite(remainder_len == bytes.len() % 4u64); assumption(); }
     have remainder_len <= 2147483647u64 by normalize() using { remainder_len <= 3u64; };

     have to_integer(b) == adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))) by { unfold(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3])))); arithmetic() using { to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) + to_integer(b_vec.0[3]); to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4; to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[1]))) * 1; to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[2]))) * 2; to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[3]))) * 3; } }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32), to_integer(at(remainder_lane_prefix, a)), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b) == adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3])))); assumption(); }
     execute_until(loop(5));
     apply(adler_general_bounded_prefix_within_full(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_general_bounded_signed_tail(bytes.len())) using { bytes.len() <= 2147483647u64; }
     apply(adler_general_bounded_tail_indices(bytes.len())) using { bytes.len() <= 2147483647u64; }
     have ((remainder_len as u32) as i32) == (((bytes.len() % 4u64) as u32) as i32) by { rewrite(remainder_len == bytes.len() % 4u64); normalize() using {}; }
     have 0 <= ((remainder_len as u32) as i32) by { rewrite(((remainder_len as u32) as i32) == (((bytes.len() % 4u64) as u32) as i32)); assumption(); }
     have ((remainder_len as u32) as i32) <= 3 by { rewrite(((remainder_len as u32) as i32) == (((bytes.len() % 4u64) as u32) as i32)); assumption(); }
     have ((remainder_len as u32) as i32) <= ((bytes.len() as u32) as i32) by { rewrite(((remainder_len as u32) as i32) == (((bytes.len() % 4u64) as u32) as i32)); assumption(); }
     have ((bytes.len() as u32) as i32) - ((remainder_len as u32) as i32) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32) by { rewrite(((remainder_len as u32) as i32) == (((bytes.len() % 4u64) as u32) as i32)); assumption(); }
     have (((__rust_mir_138_remaining as u32) as i32)) == ((remainder_len as u32) as i32) by simp() using { remainder_len <= 3u64; };
     have 0 <= (((__rust_mir_138_remaining as u32) as i32)) and (((__rust_mir_138_remaining as u32) as i32)) <= ((remainder_len as u32) as i32) by { rewrite((((__rust_mir_138_remaining as u32) as i32)) == ((remainder_len as u32) as i32)); both { assumption(); } and { normalize() using {}; } }
     have __rust_mir_138_cursor == remainder;
     have (bytes.len() - bytes.len() % 4u64) <= 2147483647u64 by arithmetic() using { bytes.len() % 4u64 <= bytes.len(); bytes.len() <= 2147483647u64; };
     apply(adler_bounded_pointer_index(bytes, bytes.len() - bytes.len() % 4u64));
     have remainder == bytes + (((bytes.len() - bytes.len() % 4u64) as u32) as i32) by simp() using { bytes + (bytes.len() - bytes.len() % 4u64) == bytes + (((bytes.len() - bytes.len() % 4u64) as u32) as i32); };
     have __rust_mir_138_cursor == bytes + (((bytes.len() as u32) as i32) - (((__rust_mir_138_remaining as u32) as i32))) by { rewrite((((__rust_mir_138_remaining as u32) as i32)) == ((remainder_len as u32) as i32)); rewrite(((bytes.len() as u32) as i32) - ((remainder_len as u32) as i32) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32)); simp() using { __rust_mir_138_cursor == remainder; remainder == bytes + (((bytes.len() - bytes.len() % 4u64) as u32) as i32); } }
     have adler_tail_consumed(((remainder_len as u32) as i32), (((__rust_mir_138_remaining as u32) as i32))) == 0 by { unfold(adler_tail_consumed(((remainder_len as u32) as i32), (((__rust_mir_138_remaining as u32) as i32)))); rewrite((((__rust_mir_138_remaining as u32) as i32)) == ((remainder_len as u32) as i32)); arithmetic() using {}; }
     have adler_tail_a_ceiling(0) == 327600 by { unfold(adler_tail_a_ceiling(0)); normalize() using {}; }
     have adler_tail_b_ceiling(0) == 1506966 by { unfold(adler_tail_b_ceiling(0)); normalize() using {}; }
     apply(uint32_to_integer_bounds(a));
     apply(uint32_to_integer_bounds(b));
     have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), (((__rust_mir_138_remaining as u32) as i32)))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), (((__rust_mir_138_remaining as u32) as i32))) == 0); rewrite(adler_tail_a_ceiling(0) == 327600); assumption(); }
     have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), (((__rust_mir_138_remaining as u32) as i32)))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), (((__rust_mir_138_remaining as u32) as i32))) == 0); rewrite(adler_tail_b_ceiling(0) == 1506966); assumption(); }
     have remainder_len <= bytes.len() by { rewrite(remainder_len == bytes.len() % 4u64); normalize(); }
     have __rust_mir_138_remaining == remainder_len;
     have __rust_mir_138_remaining <= remainder_len by { rewrite(__rust_mir_138_remaining == remainder_len); normalize(); }
     have remainder == bytes + (bytes.len() - bytes.len() % 4u64);
     have bytes.len() - __rust_mir_138_remaining == bytes.len() - bytes.len() % 4u64 by { rewrite(__rust_mir_138_remaining == remainder_len); rewrite(remainder_len == bytes.len() % 4u64); normalize(); }
     have __rust_mir_138_cursor == bytes + (bytes.len() - __rust_mir_138_remaining) by { rewrite(bytes.len() - __rust_mir_138_remaining == bytes.len() - bytes.len() % 4u64); rewrite(__rust_mir_138_cursor == remainder); assumption(); }
     have __rust_mir_138_remaining <= 3u64;
     // Connect the completed aligned prefix to the actual scalar iterator.
     have ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32) by simp();
     have old(to_integer((self.a as u32))) == to_integer(at(remainder_lane_prefix, a));
     apply(uint32_to_integer_bounds(old((self.a as u32)))) using {};
     apply(uint32_less_equal_to_integer(old((self.a as u32)), 65520u32)) using { old((self.a as u32)) <= 65520u32; };
     have ((__rust_mir_138_remaining as u32) as i32) <= ((bytes.len() as u32) as i32) by arithmetic() using { ((__rust_mir_138_remaining as u32) as i32) == ((remainder_len as u32) as i32); ((remainder_len as u32) as i32) <= ((bytes.len() as u32) as i32); };
     apply(int32_nonnegative_subtract_within_value_is_defined(((bytes.len() as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) using { 0 <= ((__rust_mir_138_remaining as u32) as i32); ((__rust_mir_138_remaining as u32) as i32) <= ((bytes.len() as u32) as i32); };
     have ((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32) by { rewrite(((__rust_mir_138_remaining as u32) as i32) == ((remainder_len as u32) as i32)); assumption(); }
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32)))) by { rewrite((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32)); rewrite((((bytes.len() - bytes.len() % 4u64) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)); rewrite(old(to_integer((self.a as u32))) == to_integer(at(remainder_lane_prefix, a))); assumption(); }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32)); rewrite((((bytes.len() - bytes.len() % 4u64) as u32) as i32) == ((((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) as u32) as i32) + ((remainder_chunk_len as u32) as i32)); rewrite(old(to_integer((self.a as u32))) == to_integer(at(remainder_lane_prefix, a))); assumption(); }
     loop {
      decreases __rust_mir_138_remaining;
      views *bytes;
      invariant bytes.len() <= 2147483647u64;
      invariant bytes.len() == old(bytes.len());
      invariant bytes == old(bytes);
      invariant forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) };
      invariant 0 <= ((remainder_len as u32) as i32) and ((remainder_len as u32) as i32) <= 3;
      invariant ((remainder_len as u32) as i32) <= ((bytes.len() as u32) as i32);
      invariant 0 <= ((bytes.len() as u32) as i32) and ((bytes.len() as u32) as i32) <= 2147483647;
      invariant 0 <= ((__rust_mir_138_remaining as u32) as i32) and ((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32);
       invariant remainder_len <= 3u64;
       invariant remainder_len <= bytes.len();
       invariant __rust_mir_138_remaining <= remainder_len;
       invariant __rust_mir_138_cursor == bytes + (bytes.len() - __rust_mir_138_remaining);
      invariant defined((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)));
      invariant 0 <= old(to_integer((self.a as u32))) and old(to_integer((self.a as u32))) <= 65520;
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32))));
      invariant truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))));
      invariant 0 <= to_integer(a) and to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)));
      invariant 0 <= to_integer(b) and to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)));
      preserve by {
        have 0u64 < __rust_mir_138_remaining;
        have 1u64 <= __rust_mir_138_remaining by arithmetic() using { 0u64 < __rust_mir_138_remaining; };
        have __rust_mir_138_remaining <= 22208u64 by arithmetic() using { __rust_mir_138_remaining <= remainder_len; remainder_len <= 3u64; };
        apply(adler_count_tail_step(__rust_mir_138_remaining)) using { 1u64 <= __rust_mir_138_remaining; __rust_mir_138_remaining <= 22208u64; }
        have 0 < ((__rust_mir_138_remaining as u32) as i32) by arithmetic() using { 1 <= ((__rust_mir_138_remaining as u32) as i32); };
       have 1 <= ((__rust_mir_138_remaining as u32) as i32) by arithmetic() using { 0 < ((__rust_mir_138_remaining as u32) as i32); };
       have 0 <= ((__rust_mir_138_remaining as u32) as i32) - 1 by arithmetic() using { 0 < ((__rust_mir_138_remaining as u32) as i32); };
       apply(int32_nonnegative_predecessor_upper_bound(((__rust_mir_138_remaining as u32) as i32), ((remainder_len as u32) as i32))) using { 0 <= ((__rust_mir_138_remaining as u32) as i32); ((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32); }
       mark tail_head;
       have 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32));
       have at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((remainder_len as u32) as i32);
       have at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32) by arithmetic() using { at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((remainder_len as u32) as i32); ((remainder_len as u32) as i32) <= ((bytes.len() as u32) as i32); };
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))));
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))));
        have 1u64 <= at(tail_head, __rust_mir_138_remaining);
        have at(tail_head, __rust_mir_138_remaining) <= remainder_len;
        have at(tail_head, __rust_mir_138_cursor) == bytes + (bytes.len() - at(tail_head, __rust_mir_138_remaining));
        have bytes.len() - at(tail_head, __rust_mir_138_remaining) < bytes.len() by arithmetic() using { 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have truncating_remainder(to_integer(at(tail_head, a)), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))), old(to_integer((self.a as u32))));
       have truncating_remainder(to_integer(at(tail_head, b)), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))));
       execute_until(assignment(byte, 0));
       have __rust_mir_155 == at(tail_head, __rust_mir_138_cursor);
        have __rust_mir_155 == bytes + (bytes.len() - at(tail_head, __rust_mir_138_remaining)) by { rewrite(__rust_mir_155 == at(tail_head, __rust_mir_138_cursor)); assumption(); }
       step();
       execute_until(assignment(__rust_mir_144, 0)); step();
       have __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64;
       have ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1 by { rewrite(__rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64); simp(); }
       have __rust_mir_138_remaining <= bytes.len() by arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have 1u64 <= bytes.len() - __rust_mir_138_remaining by arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have 0 <= ((__rust_mir_138_remaining as u32) as i32) by arithmetic() using { ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1; 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); };
       have at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1 <= ((bytes.len() as u32) as i32) by arithmetic() using { 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); };
       have ((__rust_mir_138_remaining as u32) as i32) <= ((bytes.len() as u32) as i32) by { rewrite(((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1); assumption(); }
       apply(int32_nonnegative_subtract_within_value_is_defined(((bytes.len() as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) using { 0 <= ((__rust_mir_138_remaining as u32) as i32); ((__rust_mir_138_remaining as u32) as i32) <= ((bytes.len() as u32) as i32); };
       have 1 <= (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) by arithmetic() using { ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1; 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 2147483647; };
       apply(int32_nonnegative_subtract_within_value_is_defined((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), 1)) using { 0 <= 1; 1 <= (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)); };
       have ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) == (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) by arithmetic() using { ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1; 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 2147483647; };
       have 0 <= ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) by arithmetic() using { ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) == (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))); 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 2147483647; };
       have ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) <= 2147483646 by arithmetic() using { ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) == (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))); 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 2147483647; };
       have (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) + 1 by arithmetic() using { 0 <= ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1); ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) <= 2147483646; ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) == (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))); ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1; 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 2147483647; };
       have bytes.len() - __rust_mir_138_remaining - 1u64 == bytes.len() - at(tail_head, __rust_mir_138_remaining) by arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have __rust_mir_155 == bytes + (bytes.len() - __rust_mir_138_remaining - 1u64) by { rewrite(bytes.len() - __rust_mir_138_remaining - 1u64 == bytes.len() - at(tail_head, __rust_mir_138_remaining)); assumption(); }
       have defined((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) by assumption();
       apply(adler_bounded_previous_byte_observation(bytes, bytes.len(), __rust_mir_138_remaining)) using { __rust_mir_138_remaining <= bytes.len(); 1u64 <= bytes.len() - __rust_mir_138_remaining; bytes.len() <= 2147483647u64; 0 <= ((__rust_mir_138_remaining as u32) as i32); ((__rust_mir_138_remaining as u32) as i32) <= ((bytes.len() as u32) as i32); defined((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1); };
       have __rust_mir_144 == (__rust_mir_155[0] as u32);
       apply(adler_helper_byte_observation(__rust_mir_155[0])) using {};
       have to_integer(__rust_mir_144) == to_integer(((bytes + (bytes.len() - __rust_mir_138_remaining - 1u64))[0] as i32)) by { rewrite(__rust_mir_144 == (__rust_mir_155[0] as u32)); rewrite(to_integer((__rust_mir_155[0] as u32)) == to_integer((__rust_mir_155[0] as i32))); rewrite(__rust_mir_155 == bytes + (bytes.len() - __rust_mir_138_remaining - 1u64)); normalize(); }
       have to_integer(__rust_mir_144) == to_integer((bytes[((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)] as i32)) by { rewrite(to_integer(__rust_mir_144) == to_integer(((bytes + (bytes.len() - __rust_mir_138_remaining - 1u64))[0] as i32))); assumption(); }
       have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32)))) by { rewrite(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) == (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32)))); simp(); }
       have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) == (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32)))); simp(); }
       apply(adler_prefix_a_step_one(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32))), to_integer(a))) using { 0 <= ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1); ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) <= 2147483646; 0 <= old(to_integer((self.a as u32))); 0 <= to_integer(a); truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32)))); };
       apply(adler_prefix_b_step_one(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))), to_integer(a), to_integer(b))) using { 0 <= ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1); ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) <= 2147483646; 0 <= old(to_integer((self.a as u32))); old(to_integer((self.a as u32))) <= 65520; 0 <= old(to_integer((self.b as u32))); 0 <= to_integer(a); 0 <= to_integer(b); truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32)))); truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); };
       have __rust_mir_144 <= 255u32;
       apply(uint32_less_equal_to_integer(__rust_mir_144, 255u32)) using { __rust_mir_144 <= 255u32; }
       have to_integer(__rust_mir_144) <= 255 by simp() using { to_integer(__rust_mir_144) <= to_integer(255u32); };
       apply(adler_tail_iterator_step(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32)), to_integer(a), to_integer(b), to_integer(__rust_mir_144))) using { 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); ((remainder_len as u32) as i32) <= 3; to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32)))); to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32)))); to_integer(__rust_mir_144) <= 255; }
       apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_144)) using { to_integer(a) + to_integer(__rust_mir_144) <= 4294967295; }
       execute_until(assignment(__rust_mir_146, 0));
       mark tail_add_a;
       have to_integer(at(tail_add_a, a)) == to_integer(a) by normalize();
       have to_integer(at(tail_add_a, b)) == to_integer(b) by normalize();
       have to_integer(at(tail_add_a, __rust_mir_144)) == to_integer((bytes[((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)] as i32)) by normalize() using { to_integer(__rust_mir_144) == to_integer((bytes[((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)] as i32)); };
       have truncating_remainder(to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32)))) by {
        rewrite((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) + 1);
        rewrite(to_integer(at(tail_add_a, a)) == to_integer(a));
        rewrite(to_integer(at(tail_add_a, __rust_mir_144)) == to_integer((bytes[((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)] as i32)));
        assumption();
       }
       have truncating_remainder(to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by {
        rewrite((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) + 1);
        rewrite(to_integer(at(tail_add_a, b)) == to_integer(b));
        rewrite(to_integer(at(tail_add_a, a)) == to_integer(a));
        rewrite(to_integer(at(tail_add_a, __rust_mir_144)) == to_integer((bytes[((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)] as i32)));
        assumption();
       }

       have to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) <= 4294967295;
       step();
       have __rust_mir_146 == at(tail_add_a, a) + at(tail_add_a, __rust_mir_144);
       apply(uint32_add_to_integer(at(tail_add_a, a), at(tail_add_a, __rust_mir_144))) using { to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) <= 4294967295; }
       have to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) by { rewrite(__rust_mir_146 == at(tail_add_a, a) + at(tail_add_a, __rust_mir_144)); assumption(); }
       have to_integer(__rust_mir_146) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by simp() using { to_integer(a) + to_integer(__rust_mir_144) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); };
       have to_integer(b) + to_integer(__rust_mir_146) <= 4294967295 by simp() using { to_integer(b) + to_integer(a) + to_integer(__rust_mir_144) <= 4294967295; to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); };
       have to_integer(b) + to_integer(__rust_mir_146) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by simp() using { to_integer(b) + to_integer(a) + to_integer(__rust_mir_144) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); };
       execute_until(assignment(a, 2)); step();
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1);
       have a == __rust_mir_146;
       have to_integer(a) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) by { rewrite(a == __rust_mir_146); assumption(); }
       have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32)))) by { rewrite(to_integer(a) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144))); assumption(); }
       execute_until(assignment(__rust_mir_147, 0)); step();
       have __rust_mir_147 == a;
       have a == __rust_mir_146;
       have to_integer(b) + to_integer(__rust_mir_147) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by { rewrite(__rust_mir_147 == a); rewrite(a == __rust_mir_146); assumption(); }
       have to_integer(b) + to_integer(__rust_mir_147) <= 4294967295;
       apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_147)) using { to_integer(b) + to_integer(__rust_mir_147) <= 4294967295; }
       execute_until(assignment(__rust_mir_148, 0));
       mark tail_add_b;
       have to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b));
       have to_integer(at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144));

       have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by simp() using { to_integer(b) + to_integer(__rust_mir_147) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); };
       have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= 4294967295;
       step();
       have __rust_mir_148 == at(tail_add_b, b) + at(tail_add_b, __rust_mir_147);
       apply(uint32_add_to_integer(at(tail_add_b, b), at(tail_add_b, __rust_mir_147))) using { to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= 4294967295; }

       have to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) by { rewrite(__rust_mir_148 == at(tail_add_b, b) + at(tail_add_b, __rust_mir_147)); assumption(); }
       have to_integer(__rust_mir_148) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by { rewrite(to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147))); assumption(); }
       execute_until(assignment(b, 6)); step();
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1);
       have to_integer(b) == to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)) by simp() using { to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)); to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b)); to_integer(at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144)); };
       have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b) == to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144))); assumption(); }
       execute_until(back_edge());
        have __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64;
        have ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1 by { rewrite(__rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64); simp(); }
       apply(adler_tail_remaining_progress(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32)))) using { 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((remainder_len as u32) as i32); ((remainder_len as u32) as i32) <= 3; }
       have adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)) == adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1 by { rewrite(((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1); assumption(); }
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)) == adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); assumption(); }
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)) == adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); assumption(); }
       apply(uint32_to_integer_bounds(a)); apply(uint32_to_integer_bounds(b));
       have 0 <= ((__rust_mir_138_remaining as u32) as i32) and ((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32);
       have __rust_mir_138_cursor == at(tail_head, __rust_mir_138_cursor) + 1;
        have __rust_mir_138_remaining <= remainder_len by arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; };
        have bytes.len() - at(tail_head, __rust_mir_138_remaining) <= 18446744073709551614u64 by arithmetic() using { 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
        have at(tail_head, __rust_mir_138_cursor) + 1 == bytes + ((bytes.len() - at(tail_head, __rust_mir_138_remaining)) + 1u64) by arithmetic() using { at(tail_head, __rust_mir_138_cursor) == bytes + (bytes.len() - at(tail_head, __rust_mir_138_remaining)); bytes.len() - at(tail_head, __rust_mir_138_remaining) <= 18446744073709551614u64; };
        have bytes.len() - __rust_mir_138_remaining == (bytes.len() - at(tail_head, __rust_mir_138_remaining)) + 1u64 by arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
        have __rust_mir_138_cursor == bytes + (bytes.len() - __rust_mir_138_remaining) by { rewrite(bytes.len() - __rust_mir_138_remaining == (bytes.len() - at(tail_head, __rust_mir_138_remaining)) + 1u64); simp(); }
        have __rust_mir_138_remaining < at(tail_head, __rust_mir_138_remaining) by arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); };
       apply(int32_nonnegative_subtract_within_value_is_defined(((bytes.len() as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) using { 0 <= ((__rust_mir_138_remaining as u32) as i32); ((__rust_mir_138_remaining as u32) as i32) <= ((bytes.len() as u32) as i32); };
       close_invariants by simp();
      }
     }

     execute_until(assignment(__rust_mir_149, 0));
     have at(loop(5).exit, __rust_mir_138_remaining) == 0u64 by arithmetic() using { not (0u64 < at(loop(5).exit, __rust_mir_138_remaining)); };
     have at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32)) == 0 by { rewrite(at(loop(5).exit, __rust_mir_138_remaining) == 0u64); normalize(); }
     have truncating_remainder(to_integer(at(loop(5).exit, a)), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32))), old(to_integer((self.a as u32)))) by simp();
     have to_integer(a) == to_integer(at(loop(5).exit, a)) by normalize();
     have ((bytes.len() as u32) as i32) == (((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32)) == 0); normalize(); }
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))) by { rewrite(to_integer(a) == to_integer(at(loop(5).exit, a))); rewrite(((bytes.len() as u32) as i32) == (((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32)))); assumption(); }
     have truncating_remainder(to_integer(at(loop(5).exit, b)), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32))), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by simp();
     have to_integer(b) == to_integer(at(loop(5).exit, b)) by normalize();
     have ((bytes.len() as u32) as i32) == (((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32)) == 0); normalize(); }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b) == to_integer(at(loop(5).exit, b))); rewrite(((bytes.len() as u32) as i32) == (((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32)))); assumption(); }
     have forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) } by simp();
     apply(adler_spec_extensional(bytes, old(bytes), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) using { 0 <= ((bytes.len() as u32) as i32); forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) }; }
     have adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by normalize() using { adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))) == adler_spec_a(old(bytes), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))); };
     have adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by normalize() using { adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == adler_spec_b(old(bytes), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); };
     have truncating_remainder(to_integer(a), 65521) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by arithmetic() using { truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))); adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))); };
     have truncating_remainder(to_integer(b), 65521) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by arithmetic() using { truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };
     mark tail_done;
     have truncating_remainder(to_integer(at(tail_done, a)), 65521) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by normalize() using { truncating_remainder(to_integer(a), 65521) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))); };
     have truncating_remainder(to_integer(at(tail_done, b)), 65521) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by normalize() using { truncating_remainder(to_integer(b), 65521) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };

     have __rust_checked_34 == 65521u32;
     step();
     have __rust_mir_149 == __rust_checked_32 % __rust_checked_34 by simp() using {};
     have __rust_mir_149 == __rust_checked_32 % 65521u32 by { rewrite(__rust_mir_149 == __rust_checked_32 % __rust_checked_34); rewrite(__rust_checked_34 == 65521u32); normalize(); }
     have to_integer(__rust_checked_32) == to_integer(at(tail_done, a));
     apply(uint32_remainder_to_integer(__rust_checked_32, 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(__rust_mir_149) == truncating_remainder(to_integer(__rust_checked_32), 65521) by { rewrite(__rust_mir_149 == __rust_checked_32 % 65521u32); normalize() using { to_integer(__rust_checked_32 % 65521u32) == truncating_remainder(to_integer(__rust_checked_32), to_integer(65521u32)); }; }
     have to_integer(__rust_mir_149) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by { rewrite(to_integer(__rust_mir_149) == truncating_remainder(to_integer(__rust_checked_32), 65521)); rewrite(to_integer(__rust_checked_32) == to_integer(at(tail_done, a))); assumption(); }
     apply(uint32_remainder_less_than_divisor(__rust_checked_32, 65521u32));
     have __rust_mir_149 < 65521u32 by { rewrite(__rust_mir_149 == __rust_checked_32 % 65521u32); assumption(); }
     apply(uint32_to_integer_bounds(__rust_mir_149));
     apply(uint32_less_than_to_integer(__rust_mir_149, 65521u32)) using { __rust_mir_149 < 65521u32; }
     have to_integer(__rust_mir_149) < 65521 by simp() using { to_integer(__rust_mir_149) < to_integer(65521u32); };
     have to_integer(__rust_mir_149) <= 65535 by arithmetic() using { to_integer(__rust_mir_149) < 65521; };
     mark general_reduced_a;
     execute_until(assignment(__rust_mir_151, 0));
     have __rust_checked_37 == 65521u32;
     step();
     have __rust_mir_151 == __rust_checked_35 % __rust_checked_37 by simp() using {};
     have __rust_mir_151 == __rust_checked_35 % 65521u32 by { rewrite(__rust_mir_151 == __rust_checked_35 % __rust_checked_37); rewrite(__rust_checked_37 == 65521u32); normalize(); }
     have to_integer(__rust_checked_35) == to_integer(at(tail_done, b));
     apply(uint32_remainder_to_integer(__rust_checked_35, 65521u32)) using { 65521u32 != 0u32; to_integer(65521u32) != 0; };
     have to_integer(__rust_mir_151) == truncating_remainder(to_integer(__rust_checked_35), 65521) by { rewrite(__rust_mir_151 == __rust_checked_35 % 65521u32); normalize() using { to_integer(__rust_checked_35 % 65521u32) == truncating_remainder(to_integer(__rust_checked_35), to_integer(65521u32)); }; }
     have to_integer(__rust_mir_151) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by { rewrite(to_integer(__rust_mir_151) == truncating_remainder(to_integer(__rust_checked_35), 65521)); rewrite(to_integer(__rust_checked_35) == to_integer(at(tail_done, b))); simp(); }
     apply(uint32_remainder_less_than_divisor(__rust_checked_35, 65521u32));
     have __rust_mir_151 < 65521u32 by { rewrite(__rust_mir_151 == __rust_checked_35 % 65521u32); assumption(); }
     apply(uint32_to_integer_bounds(__rust_mir_151));
     apply(uint32_less_than_to_integer(__rust_mir_151, 65521u32)) using { __rust_mir_151 < 65521u32; }
     have to_integer(__rust_mir_151) < 65521 by simp() using { to_integer(__rust_mir_151) < to_integer(65521u32); };
     have to_integer(__rust_mir_151) <= 65535 by arithmetic() using { to_integer(__rust_mir_151) < 65521; };
     mark general_reduced_b;
     execute();
     have to_integer(self.a) == to_integer(at(general_reduced_a, __rust_mir_149)) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer(at(general_reduced_a, __rust_mir_149)) => 0 <= to_integer(at(general_reduced_a, __rust_mir_149));
     premise 1: to_integer(at(general_reduced_a, __rust_mir_149)) <= 65535 => to_integer(at(general_reduced_a, __rust_mir_149)) <= 65535;
     integer_cast_identity bounds [0, 1] => to_integer(self.a) == to_integer(at(general_reduced_a, __rust_mir_149)); conclusion 0;
     } }
     have to_integer(self.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by { rewrite(to_integer(self.a) == to_integer(at(general_reduced_a, __rust_mir_149))); simp(); }
     have to_integer(at(general_reduced_a, __rust_mir_149)) < 65521;
     have to_integer(self.a) < 65521 by { rewrite(to_integer(self.a) == to_integer(at(general_reduced_a, __rust_mir_149))); assumption(); }
     have to_integer(self.b) == to_integer(at(general_reduced_b, __rust_mir_151)) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer(at(general_reduced_b, __rust_mir_151)) => 0 <= to_integer(at(general_reduced_b, __rust_mir_151));
     premise 1: to_integer(at(general_reduced_b, __rust_mir_151)) <= 65535 => to_integer(at(general_reduced_b, __rust_mir_151)) <= 65535;
     integer_cast_identity bounds [0, 1] => to_integer(self.b) == to_integer(at(general_reduced_b, __rust_mir_151)); conclusion 0;
     } }
     have to_integer(self.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by { rewrite(to_integer(self.b) == to_integer(at(general_reduced_b, __rust_mir_151))); simp(); }
     have to_integer(at(general_reduced_b, __rust_mir_151)) < 65521;
     have to_integer(self.b) < 65521 by { rewrite(to_integer(self.b) == to_integer(at(general_reduced_b, __rust_mir_151))); assumption(); }
     have 0 <= to_integer(self.a) by { rewrite(to_integer(self.a) == to_integer(at(general_reduced_a, __rust_mir_149))); simp() using { 0 <= to_integer(at(general_reduced_a, __rust_mir_149)); } }
     have to_integer(self.a) <= 65535 by arithmetic() using { to_integer(self.a) < 65521; };
     have to_integer((self.a as i32)) == to_integer(self.a) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer(self.a) => 0 <= to_integer(self.a);
     premise 1: to_integer(self.a) <= 65535 => to_integer(self.a) <= 65535;
     integer_cast_identity bounds [0, 1] => to_integer((self.a as i32)) == to_integer(self.a); conclusion 0;
     } }
     have to_integer((self.a as i32)) <= to_integer(65520) by { rewrite(to_integer((self.a as i32)) == to_integer(self.a)); arithmetic() using { to_integer(self.a) < 65521; } }
     apply(int32_to_integer_less_equal_implies_less_equal((self.a as i32), 65520)) using { to_integer((self.a as i32)) <= to_integer(65520); }
     apply(adler_i32_below_mod((self.a as i32))) using { (self.a as i32) <= 65520; }
     have self.a < 65521 by assumption();
     have 0 <= to_integer(self.b) by { rewrite(to_integer(self.b) == to_integer(at(general_reduced_b, __rust_mir_151))); simp() using { 0 <= to_integer(at(general_reduced_b, __rust_mir_151)); } }
     have to_integer(self.b) <= 65535 by arithmetic() using { to_integer(self.b) < 65521; };
     have to_integer((self.b as i32)) == to_integer(self.b) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer(self.b) => 0 <= to_integer(self.b);
     premise 1: to_integer(self.b) <= 65535 => to_integer(self.b) <= 65535;
     integer_cast_identity bounds [0, 1] => to_integer((self.b as i32)) == to_integer(self.b); conclusion 0;
     } }
     have to_integer((self.b as i32)) <= to_integer(65520) by { rewrite(to_integer((self.b as i32)) == to_integer(self.b)); arithmetic() using { to_integer(self.b) < 65521; } }
     apply(int32_to_integer_less_equal_implies_less_equal((self.b as i32), 65520)) using { to_integer((self.b as i32)) <= to_integer(65520); }
     apply(adler_i32_below_mod((self.b as i32))) using { (self.b as i32) <= 65520; }
     have self.b < 65521 by assumption();
     have to_integer(self.a) <= 65520 by arithmetic() using { to_integer(self.a) < 65521; };
     have to_integer(self.b) <= 65520 by arithmetic() using { to_integer(self.b) < 65521; };
     simp() using { self.a < 65521; self.b < 65521; to_integer(self.a) <= 65520; to_integer(self.b) <= 65520; to_integer(self.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))); to_integer(self.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); }
    }
}
