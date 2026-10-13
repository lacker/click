// Two-byte public API fragment; the harness adds public-constructors.click.
impl adler2::Adler32 {
    fn write_slice(&mut self, bytes: &[u8]) {
     requires bytes.len() == 2u64;
     requires self.a == 1;
     requires self.b == 0;
     owns self.a;
     owns self.b;
     views bytes[0..2];
     ensures to_integer(self.a) == old(adler_spec_a(bytes, 2, 1));
     ensures to_integer(self.b) == old(adler_spec_b(bytes, 2, 1, 0));
     ensures bytes[0] == old(bytes[0]);
     ensures bytes[1] == old(bytes[1]);
    } by { execute(); simp(); }
}

fn adler2::adler32_slice(data: &[u8]) -> u32 {
 requires data.len() == 2u64;
 views data[0..2];
 ensures to_integer(result) == old(adler_spec_checksum(data, 2, 1, 0));
 ensures data[0] == old(data[0]);
 ensures data[1] == old(data[1]);
} by {
 execute_until(assignment(__rust_mir_0, 0));
 have to_integer(h.a) == old(adler_spec_a(data, 2, 1));
 have to_integer(h.b) == old(adler_spec_b(data, 2, 1, 0));
 have 65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, 2, 1, 0)) by {
  unfold(adler_spec_checksum(data, 2, 1, 0));
  rewrite(to_integer(h.a) == old(adler_spec_a(data, 2, 1)));
  rewrite(to_integer(h.b) == old(adler_spec_b(data, 2, 1, 0)));
  simp();
 }
 step();
 have to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
 have to_integer(__rust_mir_0) == old(adler_spec_checksum(data, 2, 1, 0)) by arithmetic() using {
   to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
   65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, 2, 1, 0));
  };
 execute();
 simp();
}
