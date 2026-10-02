pub fn nested(bytes: &[u8]) -> usize {
    let chunks = bytes.chunks_exact(4);
    let tail = chunks.remainder();
    for chunk in chunks {
        for part in chunk.chunks_exact(2) {
            let first = part[0];
            let last = part[1];
        }
    }
    tail.len()
}

pub fn array_len() -> usize {
    let bytes = [7u8; 8];
    let slice: &[u8] = &bytes;
    slice.len()
}

pub fn array_mut() -> u8 {
    let mut bytes = [7u8; 8];
    let slice: &mut [u8] = &mut bytes;
    slice[3] = 9;
    slice[3]
}

pub fn array_chunks() -> usize {
    let bytes = [7u8; 8];
    let chunks = bytes.chunks_exact(4);
    let tail = chunks.remainder();
    for chunk in chunks { let first = chunk[0]; }
    tail.len()
}

pub fn empty_array_len() -> usize {
    let bytes = [7u8; 0];
    let slice: &[u8] = &bytes;
    slice.len()
}

pub fn medium_array_len() -> usize {
    let bytes = [7u8; 1024];
    let slice: &[u8] = &bytes;
    slice.len()
}

pub fn large_array_len() -> usize {
    let bytes = [7u8; 1_000_000];
    let slice: &[u8] = &bytes;
    slice.len()
}

pub fn array_read(index: usize) -> u8 {
    let bytes = [7u8; 8];
    let slice: &[u8] = &bytes;
    slice[index]
}
