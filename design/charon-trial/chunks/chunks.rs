pub fn tail(bytes: &[u8], size: usize) -> usize {
    let chunks = bytes.chunks_exact(size);
    chunks.remainder().len()
}
pub fn walk(bytes: &[u8]) -> usize {
    let chunks = bytes.chunks_exact(4);
    let tail = chunks.remainder();
    for chunk in chunks { let first = chunk[0]; let last = chunk[3]; }
    tail.len()
}

pub fn next_len(bytes: &[u8]) -> usize {
    let mut chunks = bytes.chunks_exact(4);
    match chunks.next() {
        Some(chunk) => chunk.len(),
        None => 0,
    }
}

pub fn tail_byte(bytes: &[u8]) -> u8 {
    let chunks = bytes.chunks_exact(4);
    let tail = chunks.remainder();
    tail[0]
}
