pub struct Packet {
    pub prefix: u32,
    pub words: [u32; 4],
    pub marker: u32,
}
pub struct Words(pub [u32; 4]);
pub struct Bytes {
    pub bytes: [u8; 7],
    pub marker: u8,
}
pub struct Empty {
    pub bytes: [u8; 0],
    pub marker: u8,
}
pub fn construct(value: u32, index: usize) -> u32 {
    let packet = Packet { prefix: 11, words: [value; 4], marker: 17 };
    packet.words[index]
}
pub fn moved(value: u32, index: usize) -> u32 {
    let packet = Packet { prefix: 11, words: [value; 4], marker: 17 };
    let next = packet;
    next.words[index]
}
pub fn reassigned(value: u32, replacement: u32) -> u32 {
    let mut packet = Packet { prefix: 11, words: [value; 4], marker: 17 };
    packet.words = [replacement; 4];
    packet.words[3]
}
pub fn neighboring_fields(value: u32, replacement: u32) -> u32 {
    let mut packet = Packet { prefix: 11, words: [value; 4], marker: 17 };
    packet.words = [replacement; 4];
    packet.prefix + packet.marker
}
pub fn extracted(value: u32, index: usize) -> u32 {
    let packet = Packet { prefix: 11, words: [value; 4], marker: 17 };
    let words = packet.words;
    words[index]
}
pub fn copied_value(value: u32) -> u32 {
    let mut packet = Packet { prefix: 11, words: [value; 4], marker: 17 };
    let words = packet.words;
    packet.words[0] = 99;
    words[0]
}
pub fn tuple_move(value: u32) -> u32 {
    let words = Words([value; 4]);
    let next = words;
    next.0[2]
}
pub fn byte_move(value: u8) -> u8 {
    let bytes = Bytes { bytes: [value; 7], marker: 31 };
    let next = bytes;
    next.bytes[6]
}
pub fn empty_move(value: u8) -> u8 {
    let empty = Empty { bytes: [value; 0], marker: 31 };
    let next = empty;
    next.marker
}
