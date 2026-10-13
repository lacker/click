# Save and restore the prefix checksum before updating the unchanged suffix.
fn adler_resumed::resumed(bytes: &[u8], split: usize) -> u32 {
 requires bytes.len() <= 2147483647u64;
 requires split <= bytes.len();
 views *bytes;
 ensures forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) };
 ensures to_integer(result) == old(adler_spec_checksum(bytes, ((bytes.len() as u32) as i32), 1, 0));
} by {
 apply(adler_incremental_split(bytes.len(), split)) using { bytes.len() <= 2147483647u64; split <= bytes.len(); }
 apply(adler_bounded_pointer_index(bytes, split)) using { split <= 2147483647u64; }
 execute_until(assignment(__rust_mir_10, 0));
 have prefix_len == split by simp();
 have suffix_len == bytes.len() - split by simp();
 have prefix == bytes by simp();
 have suffix == bytes + split by simp();
 have __rust_mir_8.a == 1 by simp();
 have __rust_mir_8.b == 0 by simp();
 have to_integer((__rust_mir_8.a as u32)) == 1 by { rewrite(__rust_mir_8.a == 1); normalize(); }
 have to_integer((__rust_mir_8.b as u32)) == 0 by { rewrite(__rust_mir_8.b == 0); normalize(); }
 mark initial_seed;
 execute_until(assignment(__rust_mir_13, 0));
 have to_integer(__rust_mir_8.a) == old(adler_spec_a(bytes, ((split as u32) as i32), 1)) by { rewrite(1 == at(initial_seed, to_integer((__rust_mir_8.a as u32)))); assumption(); }
 have to_integer(__rust_mir_8.b) == old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)) by { rewrite(1 == at(initial_seed, to_integer((__rust_mir_8.a as u32)))); rewrite(0 == at(initial_seed, to_integer((__rust_mir_8.b as u32)))); assumption(); }
 apply(adler_u16_observation(__rust_mir_8.a));
 apply(adler_u16_observation(__rust_mir_8.b));
 have to_integer((__rust_mir_8.a as u32)) == old(adler_spec_a(bytes, ((split as u32) as i32), 1)) by arithmetic() using { to_integer((__rust_mir_8.a as u32)) == to_integer(__rust_mir_8.a); to_integer(__rust_mir_8.a) == old(adler_spec_a(bytes, ((split as u32) as i32), 1)); };
 have to_integer((__rust_mir_8.b as u32)) == old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)) by arithmetic() using { to_integer((__rust_mir_8.b as u32)) == to_integer(__rust_mir_8.b); to_integer(__rust_mir_8.b) == old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)); };
 apply(uint32_less_equal_to_integer((__rust_mir_8.a as u32), 65520u32));
 have to_integer((__rust_mir_8.a as u32)) <= to_integer(65535u32) by arithmetic() using { to_integer((__rust_mir_8.a as u32)) <= to_integer(65520u32); };
 apply(uint32_to_integer_less_equal_implies_less_equal((__rust_mir_8.a as u32), 65535u32));
 apply(uint32_less_equal_to_integer((__rust_mir_8.b as u32), 65520u32));
 have to_integer((__rust_mir_8.b as u32)) <= to_integer(65535u32) by arithmetic() using { to_integer((__rust_mir_8.b as u32)) <= to_integer(65520u32); };
 apply(uint32_to_integer_less_equal_implies_less_equal((__rust_mir_8.b as u32), 65535u32));
 mark saved_state;
 apply(uint32_unpack_uint16_low((__rust_mir_8.a as u32), (__rust_mir_8.b as u32)));
 apply(uint32_unpack_uint16_high((__rust_mir_8.a as u32), (__rust_mir_8.b as u32)));
 execute_until(assignment(__rust_mir_17, 0));
 have saved == at(saved_state, ((__rust_mir_8.b as u32) << 16) | (__rust_mir_8.a as u32)) by assumption();
 have (__rust_mir_14.a as u32) == at(saved_state, (__rust_mir_8.a as u32)) by {
  rewrite((__rust_mir_14.a as u32) == (saved & 65535u32));
  rewrite(saved == at(saved_state, ((__rust_mir_8.b as u32) << 16) | (__rust_mir_8.a as u32)));
  assumption();
 }
 have (__rust_mir_14.b as u32) == at(saved_state, (__rust_mir_8.b as u32)) by {
  rewrite((__rust_mir_14.b as u32) == ((saved >> 16) & 65535u32));
  rewrite(saved == at(saved_state, ((__rust_mir_8.b as u32) << 16) | (__rust_mir_8.a as u32)));
  assumption();
 }
 have (__rust_mir_14.a as u32) <= 65520u32 by { rewrite((__rust_mir_14.a as u32) == at(saved_state, (__rust_mir_8.a as u32))); assumption(); }
 have (__rust_mir_14.b as u32) <= 65520u32 by { rewrite((__rust_mir_14.b as u32) == at(saved_state, (__rust_mir_8.b as u32))); assumption(); }
 have to_integer((__rust_mir_14.a as u32)) == old(adler_spec_a(bytes, ((split as u32) as i32), 1)) by { rewrite((__rust_mir_14.a as u32) == at(saved_state, (__rust_mir_8.a as u32))); assumption(); }
 have to_integer((__rust_mir_14.b as u32)) == old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)) by { rewrite((__rust_mir_14.b as u32) == at(saved_state, (__rust_mir_8.b as u32))); assumption(); }
 mark prefix_done;
 have suffix == bytes + ((split as u32) as i32) by { rewrite(suffix == bytes + split); assumption(); }
 have forall (k: int32) { 0 <= k and k < (((bytes.len() - split) as u32) as i32) implies suffix[k] == old((bytes + ((split as u32) as i32))[k]) } by {
  intro(); intro();
  extract(0 <= k); extract(k < (((bytes.len() - split) as u32) as i32));
  apply(adler_bounded_signed_index(bytes.len() - split, k)) using { bytes.len() - split <= 2147483647u64; 0 <= k; k < (((bytes.len() - split) as u32) as i32); }
  rewrite(suffix == bytes + ((split as u32) as i32));
  normalize();
 }
 apply(adler_spec_extensional(suffix, old(bytes + ((split as u32) as i32)), (((bytes.len() - split) as u32) as i32), to_integer((__rust_mir_14.a as u32)), to_integer((__rust_mir_14.b as u32)))) using {
  0 <= (((bytes.len() - split) as u32) as i32);
  forall (k: int32) { 0 <= k and k < (((bytes.len() - split) as u32) as i32) implies suffix[k] == old((bytes + ((split as u32) as i32))[k]) };
 }
 execute_until(assignment(__rust_mir_0, 0));
 have to_integer(__rust_mir_14.a) == at(prefix_done, adler_spec_a(suffix, (((bytes.len() - split) as u32) as i32), to_integer((__rust_mir_14.a as u32)))) by assumption();
 have to_integer(__rust_mir_14.b) == at(prefix_done, adler_spec_b(suffix, (((bytes.len() - split) as u32) as i32), to_integer((__rust_mir_14.a as u32)), to_integer((__rust_mir_14.b as u32)))) by assumption();
 have at(prefix_done, adler_spec_a(suffix, (((bytes.len() - split) as u32) as i32), to_integer((__rust_mir_14.a as u32)))) == old(adler_spec_a(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), at(prefix_done, to_integer((__rust_mir_14.a as u32))))) by assumption();
 have at(prefix_done, adler_spec_b(suffix, (((bytes.len() - split) as u32) as i32), to_integer((__rust_mir_14.a as u32)), to_integer((__rust_mir_14.b as u32)))) == old(adler_spec_b(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), at(prefix_done, to_integer((__rust_mir_14.a as u32))), at(prefix_done, to_integer((__rust_mir_14.b as u32))))) by assumption();
 have to_integer(__rust_mir_14.a) == old(adler_spec_a(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), old(adler_spec_a(bytes, ((split as u32) as i32), 1)))) by {
  rewrite(old(adler_spec_a(bytes, ((split as u32) as i32), 1)) == at(prefix_done, to_integer((__rust_mir_14.a as u32))));
  rewrite(old(adler_spec_a(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), at(prefix_done, to_integer((__rust_mir_14.a as u32))))) == at(prefix_done, adler_spec_a(suffix, (((bytes.len() - split) as u32) as i32), to_integer((__rust_mir_14.a as u32)))));
  assumption();
 }
 have to_integer(__rust_mir_14.b) == old(adler_spec_b(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), old(adler_spec_a(bytes, ((split as u32) as i32), 1)), old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)))) by {
  rewrite(old(adler_spec_a(bytes, ((split as u32) as i32), 1)) == at(prefix_done, to_integer((__rust_mir_14.a as u32))));
  rewrite(old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)) == at(prefix_done, to_integer((__rust_mir_14.b as u32))));
  rewrite(old(adler_spec_b(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), at(prefix_done, to_integer((__rust_mir_14.a as u32))), at(prefix_done, to_integer((__rust_mir_14.b as u32))))) == at(prefix_done, adler_spec_b(suffix, (((bytes.len() - split) as u32) as i32), to_integer((__rust_mir_14.a as u32)), to_integer((__rust_mir_14.b as u32)))));
  assumption();
 }
 apply(adler_spec_a_concat(bytes, ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), 1));
 apply(adler_spec_b_concat(bytes, ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), 1, 0));
 have to_integer(__rust_mir_14.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), 1)) by {
  rewrite(((bytes.len() as u32) as i32) == ((split as u32) as i32) + (((bytes.len() - split) as u32) as i32));
  rewrite(adler_spec_a(bytes, ((split as u32) as i32) + (((bytes.len() - split) as u32) as i32), 1) == adler_spec_a(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), adler_spec_a(bytes, ((split as u32) as i32), 1)));
  assumption();
 }
 have to_integer(__rust_mir_14.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), 1, 0)) by {
  rewrite(((bytes.len() as u32) as i32) == ((split as u32) as i32) + (((bytes.len() - split) as u32) as i32));
  rewrite(adler_spec_b(bytes, ((split as u32) as i32) + (((bytes.len() - split) as u32) as i32), 1, 0) == adler_spec_b(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), adler_spec_a(bytes, ((split as u32) as i32), 1), adler_spec_b(bytes, ((split as u32) as i32), 1, 0)));
  assumption();
 }
 have 65536 * to_integer(__rust_mir_14.b) + to_integer(__rust_mir_14.a) == old(adler_spec_checksum(bytes, ((bytes.len() as u32) as i32), 1, 0)) by {
  unfold(adler_spec_checksum(bytes, ((bytes.len() as u32) as i32), 1, 0));
  rewrite(to_integer(__rust_mir_14.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), 1)));
  rewrite(to_integer(__rust_mir_14.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), 1, 0)));
  normalize();
 }
 step();
 have to_integer(__rust_mir_0) == old(adler_spec_checksum(bytes, ((bytes.len() as u32) as i32), 1, 0)) by arithmetic() using {
  to_integer(__rust_mir_0) == 65536 * to_integer(__rust_mir_14.b) + to_integer(__rust_mir_14.a);
  65536 * to_integer(__rust_mir_14.b) + to_integer(__rust_mir_14.a) == old(adler_spec_checksum(bytes, ((bytes.len() as u32) as i32), 1, 0));
 };
 have forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) } by {
  intro(); intro();
  extract(0 <= k); extract(k < ((bytes.len() as u32) as i32));
  apply(adler_bounded_signed_index(bytes.len(), k)) using { bytes.len() <= 2147483647u64; 0 <= k; k < ((bytes.len() as u32) as i32); }
  simp();
 }
 execute(); simp();
}
