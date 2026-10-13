#[path = "src/lib.rs"]
mod adler2;
pub use adler2::Adler32;

pub fn resumed(bytes: &[u8], split: usize) -> u32 {
    let (prefix, suffix) = bytes.split_at(split);
    let mut state = adler2::Adler32::new();
    state.write_slice(prefix);
    let saved = state.checksum();
    let mut state = adler2::Adler32::from_checksum(saved);
    state.write_slice(suffix);
    state.checksum()
}
