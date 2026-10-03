pub struct Lanes { pub values: [u32; 4], pub marker: u8 }
pub struct Words(pub [u32; 4]);
pub struct Bytes { pub prefix: u32, pub bytes: [u8; 7] }
pub struct Empty { pub empty: [u8; 0], pub marker: u8 }
pub fn read(state: &Lanes, index: usize) -> u32 { state.values[index] }
pub fn write(state: &mut Lanes, index: usize, value: u32) { state.values[index] = value; }
pub fn array_first(values: &[u32; 4]) -> u32 { values[0] }
pub fn borrowed_first(state: &Lanes) -> u32 { array_first(&state.values) }
pub fn tuple_read(state: &Words, index: usize) -> u32 { state.0[index] }
pub fn byte_read(state: &Bytes, index: usize) -> u8 { state.bytes[index] }
pub fn slice_first(bytes: &[u8]) -> u8 { bytes[0] }
pub fn borrowed_byte(state: &Bytes) -> u8 { slice_first(&state.bytes) }
pub fn empty_len(state: &Empty) -> usize { state.empty.len() }
