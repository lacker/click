pub struct Packet {
    pub prefix: u32,
    pub words: [u32; 4],
    pub marker: u32,
}
pub struct Signed(pub [i32; 3]);
pub struct Bytes(pub [u8; 3]);

pub fn computed_move(a: u32, b: u32) -> u32 {
    let packet = Packet { prefix: 11, words: [a, b ^ 1, 3, 4], marker: 17 };
    let next = packet;
    next.words[1]
}
pub fn source_write(a: u32, b: u32) -> u32 {
    let mut packet = Packet { prefix: 11, words: [a, b, 3, 4], marker: 17 };
    let words = packet.words;
    packet.words[0] = 99;
    words[0]
}
pub fn target_write(a: u32, b: u32) -> u32 {
    let packet = Packet { prefix: 11, words: [a, b, 3, 4], marker: 17 };
    let mut words = packet.words;
    words[1] = 99;
    packet.words[1]
}
pub fn replacement(a: u32, b: u32) -> u32 {
    let mut packet = Packet { prefix: 11, words: [a; 4], marker: 17 };
    packet.words = [b, a, 3, 4];
    let next = packet;
    next.words[0]
}
pub fn neighbors(a: u32, b: u32) -> u32 {
    let mut packet = Packet { prefix: 11, words: [a; 4], marker: 17 };
    packet.words = [b, a, 3, 4];
    packet.prefix + packet.marker
}
pub fn sparse(a: u32, b: u32) -> u32 {
    let mut source = [a; 1024];
    source[3] = b;
    let target = source;
    source[3] = 99;
    target[3]
}
pub fn signed(a: i32, b: i32) -> i32 {
    let words = Signed([a, b, -3]);
    let next = words;
    next.0[1]
}
pub fn bytes(a: u8, b: u8) -> u8 {
    let words = Bytes([a, b, 3]);
    let next = words;
    next.0[1]
}
