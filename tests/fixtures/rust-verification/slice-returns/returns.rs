// Slice returns: a function that returns `&[T]`, `&mut [T]` or `&str`
// returns one wide value, its data pointer and its length.

pub fn whole(bytes: &[u8]) -> &[u8] {
    bytes
}

pub fn passed(bytes: &[u8]) -> &[u8] {
    whole(bytes)
}

pub fn measured(bytes: &[u8]) -> usize {
    let view = whole(bytes);
    view.len()
}

pub fn same(bytes: &[u8]) -> &[u8] {
    bytes
}

pub fn exclusive(bytes: &mut [u8]) -> &mut [u8] {
    bytes
}

pub fn named(s: &str) -> &str {
    s
}

pub fn copied(bytes: &[u8]) -> u8 {
    let view = bytes;
    view[0]
}

pub fn first(bytes: &[u8]) -> u8 {
    let view = whole(bytes);
    view[0]
}
