verifying "bytes.rs";

// `s.as_bytes()` calls the library's `str::as_bytes`, whose contract gives
// the string's bytes as a byte slice: the same data pointer and length.
fn str_bytes::byte_count(s: &str) -> usize {
    ensures result == s.len();
}

// The byte view has the string's length, so its first byte is in bounds
// whenever the string is not empty, and it is the string's first byte.
fn str_bytes::first_byte(s: &str) -> u8 {
    requires 0u64 < s.len();
    views *s;
    ensures result == click::rust::str::as_bytes(s)[0];
}
