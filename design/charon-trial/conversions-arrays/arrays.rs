pub struct Guard<'a> {
    pub slot: &'a mut i32,
    pub saved: i32,
}
impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.slot = self.saved;
    }
}
pub fn guarded_array(value: &mut i32, x: u16) -> u32 {
    let saved = *value;
    let guard = Guard { slot: value, saved };
    *guard.slot = 7;
    let lanes = [u32::from(x); 4];
    let copy = lanes;
    copy[3]
}
pub fn large_array() -> u8 {
    let bytes = [7u8; 1_000_000];
    let copy = bytes;
    copy[999_999]
}
pub fn increment(value: &mut i32) -> u8 {
    *value += 1;
    7
}
pub fn empty_array(value: &mut i32) {
    let bytes = [increment(value); 0];
    let _copy = bytes;
}
pub fn explicit_array() -> u32 {
    let mut values = [1u32, 2, 3];
    values[1] = 9;
    values[1]
}
pub fn cast_array(x: u32) -> u8 {
    let bytes = [x as u8; 1];
    bytes[0]
}
