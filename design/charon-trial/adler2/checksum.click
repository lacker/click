// Contract fragment for the unchanged shared checksum getter.
// The harness combines this with packing.click and the locked crate import.
impl adler2::Adler32 {
    fn checksum(&self) -> u32 {
     views self.a;
     views self.b;
     ensures to_integer(result) == 65536 * old(to_integer(self.b)) + old(to_integer(self.a));
     ensures self.a == old(self.a);
     ensures self.b == old(self.b);
     ensures result == old(((self.b as u32) << 16) | (self.a as u32));
    } by {
     apply(adler_pack_fields(self.a, self.b));
     execute();
     have result == old(((self.b as u32) << 16) | (self.a as u32));
     rewrite(result == old(((self.b as u32) << 16) | (self.a as u32)));
     simp();
    }
}
