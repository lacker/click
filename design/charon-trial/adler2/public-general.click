# General public API composition; the harness checks all unchanged callee bodies.
impl adler2::Adler32 {
    fn write_slice(&mut self, bytes: &[u8]) {
     requires bytes.len() <= 2147483647u64;
     requires (self.a as u32) <= 65520u32;
     requires (self.b as u32) <= 65520u32;
     owns self.a;
     owns self.b;
     views *bytes;
     ensures to_integer(self.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))));
     ensures to_integer(self.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
     ensures self.a < 65521;
     ensures self.b < 65521;
     ensures (self.a as u32) <= 65520u32;
     ensures (self.b as u32) <= 65520u32;
     ensures forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) };
    } by {
     apply(adler_bounded_count(bytes.len())) using { bytes.len() <= 2147483647u64; }
     execute();
     apply(adler_canonical_observation(self.a));
     apply(adler_canonical_observation(self.b));
     have forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) } by {
      intro(); intro();
      extract(0 <= k); extract(k < ((bytes.len() as u32) as i32));
      apply(adler_bounded_signed_index(bytes.len(), k)) using { bytes.len() <= 2147483647u64; 0 <= k; k < ((bytes.len() as u32) as i32); }
      simp();
     }
     simp();
    }
}

fn adler2::adler32_slice(data: &[u8]) -> u32 {
 requires data.len() <= 2147483647u64;
 views *data;
 ensures forall (k: int32) { 0 <= k and k < ((data.len() as u32) as i32) implies data[k] == old(data[k]) };
 ensures to_integer(result) == old(adler_spec_checksum(data, ((data.len() as u32) as i32), 1, 0));
} by {
 apply(adler_bounded_count(data.len())) using { data.len() <= 2147483647u64; }
 execute_until(assignment(__rust_mir_4, 0));
 have h.a == 1 by simp();
 have h.b == 0 by simp();
 have to_integer((h.a as u32)) == 1 by { rewrite(h.a == 1); normalize(); }
 have to_integer((h.b as u32)) == 0 by { rewrite(h.b == 0); normalize(); }
 mark canonical_seed;
 execute_until(assignment(__rust_mir_0, 0));
 have forall (k: int32) { 0 <= k and k < ((data.len() as u32) as i32) implies data[k] == old(data[k]) } by simp();
 have to_integer(h.a) == old(adler_spec_a(data, ((data.len() as u32) as i32), 1)) by {
  rewrite(1 == at(canonical_seed, to_integer((h.a as u32))));
  assumption();
 }
 have to_integer(h.b) == old(adler_spec_b(data, ((data.len() as u32) as i32), 1, 0)) by {
  rewrite(1 == at(canonical_seed, to_integer((h.a as u32))));
  rewrite(0 == at(canonical_seed, to_integer((h.b as u32))));
  assumption();
 }
 have 65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, ((data.len() as u32) as i32), 1, 0)) by {
  unfold(adler_spec_checksum(data, ((data.len() as u32) as i32), 1, 0));
  rewrite(to_integer(h.a) == old(adler_spec_a(data, ((data.len() as u32) as i32), 1)));
  rewrite(to_integer(h.b) == old(adler_spec_b(data, ((data.len() as u32) as i32), 1, 0)));
  simp();
 }
 step();
 have to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
 have to_integer(__rust_mir_0) == old(adler_spec_checksum(data, ((data.len() as u32) as i32), 1, 0)) by arithmetic() using {
   to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
   65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, ((data.len() as u32) as i32), 1, 0));
  };
 execute();
 simp();
}
