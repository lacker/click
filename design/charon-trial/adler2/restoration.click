// Exact word observations for the unchanged saved-checksum constructor.
// All uint32 inputs are supported, including noncanonical Adler seeds.
verifying "src/lib.rs";
impl adler2::Adler32 {
    fn from_checksum(sum: u32) -> adler2::Adler32 {
     ensures (result.a as u32) == old(sum & 65535u32);
     ensures (result.b as u32) == old((sum >> 16) & 65535u32);
    } by { execute(); simp(); }
}
