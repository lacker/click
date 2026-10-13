#[path = "src/lib.rs"]
mod adler2;
pub use adler2::Adler32;

pub fn incremental(bytes: &[u8], split: usize) -> u32 {
    let (prefix, suffix) = bytes.split_at(split);
    let mut state = adler2::Adler32::new();
    state.write_slice(prefix);
    state.write_slice(suffix);
    state.checksum()
}
