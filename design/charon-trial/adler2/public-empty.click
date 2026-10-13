// Empty public API fragment; no input-byte authority or dereference is needed.
impl adler2::Adler32 {
    fn write_slice(&mut self, bytes: &[u8]) {
     requires bytes.len() == 0u64;
     requires self.a == 1;
     requires self.b == 0;
     owns self.a;
     owns self.b;
     views bytes[0..0];
     ensures self.a == 1;
     ensures self.b == 0;
    } by { execute(); simp(); }
}

fn adler2::adler32_slice(data: &[u8]) -> u32 {
 requires data.len() == 0u64;
 views data[0..0];
 ensures to_integer(result) == old(adler_spec_checksum(data, 0, 1, 0));
} by {
 apply(adler_spec_empty(data, 1, 0));
 unfold(adler_spec_checksum(data, 0, 1, 0));
 execute_until(assignment(__rust_mir_0, 0));
 have to_integer(h.a) == old(adler_spec_a(data, 0, 1)) by {
  rewrite(old(adler_spec_a(data, 0, 1)) == 1);
  rewrite(h.a == 1);
  simp();
 }
 have to_integer(h.b) == old(adler_spec_b(data, 0, 1, 0)) by {
  rewrite(old(adler_spec_b(data, 0, 1, 0)) == 0);
  rewrite(h.b == 0);
  simp();
 }
 have 65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, 0, 1, 0)) by {
  rewrite(to_integer(h.a) == old(adler_spec_a(data, 0, 1)));
  rewrite(to_integer(h.b) == old(adler_spec_b(data, 0, 1, 0)));
  simp();
 }
 step();
 have to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
 have to_integer(__rust_mir_0) == old(adler_spec_checksum(data, 0, 1, 0)) by arithmetic() using {
   to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
   65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, 0, 1, 0));
  };
 execute();
 simp();
}
