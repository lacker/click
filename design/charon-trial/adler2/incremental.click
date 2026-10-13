// Real two-update client of the unchanged pinned library.
fn adler_incremental::incremental(bytes: &[u8], split: usize) -> u32 {
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
 have state.a == 1 by simp();
 have state.b == 0 by simp();
 have to_integer((state.a as u32)) == 1 by { rewrite(state.a == 1); normalize(); }
 have to_integer((state.b as u32)) == 0 by { rewrite(state.b == 0); normalize(); }
 mark initial_seed;
 execute_until(assignment(__rust_mir_13, 0));
 have to_integer(state.a) == old(adler_spec_a(bytes, ((split as u32) as i32), 1)) by { rewrite(1 == at(initial_seed, to_integer((state.a as u32)))); assumption(); }
 have to_integer(state.b) == old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)) by { rewrite(1 == at(initial_seed, to_integer((state.a as u32)))); rewrite(0 == at(initial_seed, to_integer((state.b as u32)))); assumption(); }
 apply(adler_u16_observation(state.a));
 apply(adler_u16_observation(state.b));
 have to_integer((state.a as u32)) == old(adler_spec_a(bytes, ((split as u32) as i32), 1)) by arithmetic() using { to_integer((state.a as u32)) == to_integer(state.a); to_integer(state.a) == old(adler_spec_a(bytes, ((split as u32) as i32), 1)); };
 have to_integer((state.b as u32)) == old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)) by arithmetic() using { to_integer((state.b as u32)) == to_integer(state.b); to_integer(state.b) == old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)); };
 mark prefix_done;
 have suffix == bytes + ((split as u32) as i32) by { rewrite(suffix == bytes + split); assumption(); }
 have forall (k: int32) { 0 <= k and k < (((bytes.len() - split) as u32) as i32) implies suffix[k] == old((bytes + ((split as u32) as i32))[k]) } by {
  intro(); intro();
  extract(0 <= k); extract(k < (((bytes.len() - split) as u32) as i32));
  apply(adler_bounded_signed_index(bytes.len() - split, k)) using { bytes.len() - split <= 2147483647u64; 0 <= k; k < (((bytes.len() - split) as u32) as i32); }
  rewrite(suffix == bytes + ((split as u32) as i32));
  normalize();
 }
 apply(adler_spec_extensional(suffix, old(bytes + ((split as u32) as i32)), (((bytes.len() - split) as u32) as i32), to_integer((state.a as u32)), to_integer((state.b as u32)))) using {
  0 <= (((bytes.len() - split) as u32) as i32);
  forall (k: int32) { 0 <= k and k < (((bytes.len() - split) as u32) as i32) implies suffix[k] == old((bytes + ((split as u32) as i32))[k]) };
 }
 execute_until(assignment(__rust_mir_0, 0));
 have to_integer(state.a) == at(prefix_done, adler_spec_a(suffix, (((bytes.len() - split) as u32) as i32), to_integer((state.a as u32)))) by assumption();
 have to_integer(state.b) == at(prefix_done, adler_spec_b(suffix, (((bytes.len() - split) as u32) as i32), to_integer((state.a as u32)), to_integer((state.b as u32)))) by assumption();
 have at(prefix_done, adler_spec_a(suffix, (((bytes.len() - split) as u32) as i32), to_integer((state.a as u32)))) == old(adler_spec_a(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), at(prefix_done, to_integer((state.a as u32))))) by assumption();
 have at(prefix_done, adler_spec_b(suffix, (((bytes.len() - split) as u32) as i32), to_integer((state.a as u32)), to_integer((state.b as u32)))) == old(adler_spec_b(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), at(prefix_done, to_integer((state.a as u32))), at(prefix_done, to_integer((state.b as u32))))) by assumption();
 have to_integer(state.a) == old(adler_spec_a(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), old(adler_spec_a(bytes, ((split as u32) as i32), 1)))) by {
  rewrite(old(adler_spec_a(bytes, ((split as u32) as i32), 1)) == at(prefix_done, to_integer((state.a as u32))));
  rewrite(old(adler_spec_a(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), at(prefix_done, to_integer((state.a as u32))))) == at(prefix_done, adler_spec_a(suffix, (((bytes.len() - split) as u32) as i32), to_integer((state.a as u32)))));
  assumption();
 }
 have to_integer(state.b) == old(adler_spec_b(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), old(adler_spec_a(bytes, ((split as u32) as i32), 1)), old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)))) by {
  rewrite(old(adler_spec_a(bytes, ((split as u32) as i32), 1)) == at(prefix_done, to_integer((state.a as u32))));
  rewrite(old(adler_spec_b(bytes, ((split as u32) as i32), 1, 0)) == at(prefix_done, to_integer((state.b as u32))));
  rewrite(old(adler_spec_b(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), at(prefix_done, to_integer((state.a as u32))), at(prefix_done, to_integer((state.b as u32))))) == at(prefix_done, adler_spec_b(suffix, (((bytes.len() - split) as u32) as i32), to_integer((state.a as u32)), to_integer((state.b as u32)))));
  assumption();
 }
 apply(adler_spec_a_concat(bytes, ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), 1));
 apply(adler_spec_b_concat(bytes, ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), 1, 0));
 have to_integer(state.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), 1)) by {
  rewrite(((bytes.len() as u32) as i32) == ((split as u32) as i32) + (((bytes.len() - split) as u32) as i32));
  rewrite(adler_spec_a(bytes, ((split as u32) as i32) + (((bytes.len() - split) as u32) as i32), 1) == adler_spec_a(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), adler_spec_a(bytes, ((split as u32) as i32), 1)));
  assumption();
 }
 have to_integer(state.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), 1, 0)) by {
  rewrite(((bytes.len() as u32) as i32) == ((split as u32) as i32) + (((bytes.len() - split) as u32) as i32));
  rewrite(adler_spec_b(bytes, ((split as u32) as i32) + (((bytes.len() - split) as u32) as i32), 1, 0) == adler_spec_b(bytes + ((split as u32) as i32), (((bytes.len() - split) as u32) as i32), adler_spec_a(bytes, ((split as u32) as i32), 1), adler_spec_b(bytes, ((split as u32) as i32), 1, 0)));
  assumption();
 }
 have 65536 * to_integer(state.b) + to_integer(state.a) == old(adler_spec_checksum(bytes, ((bytes.len() as u32) as i32), 1, 0)) by {
  unfold(adler_spec_checksum(bytes, ((bytes.len() as u32) as i32), 1, 0));
  rewrite(to_integer(state.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), 1)));
  rewrite(to_integer(state.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), 1, 0)));
  normalize();
 }
 step();
 have to_integer(__rust_mir_0) == old(adler_spec_checksum(bytes, ((bytes.len() as u32) as i32), 1, 0)) by arithmetic() using {
  to_integer(__rust_mir_0) == 65536 * to_integer(state.b) + to_integer(state.a);
  65536 * to_integer(state.b) + to_integer(state.a) == old(adler_spec_checksum(bytes, ((bytes.len() as u32) as i32), 1, 0));
 };
 have forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) } by {
  intro(); intro();
  extract(0 <= k); extract(k < ((bytes.len() as u32) as i32));
  apply(adler_bounded_signed_index(bytes.len(), k)) using { bytes.len() <= 2147483647u64; 0 <= k; k < ((bytes.len() as u32) as i32); }
  simp();
 }
 execute(); simp();
}
