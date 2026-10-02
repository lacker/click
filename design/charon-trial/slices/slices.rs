pub fn length(bytes: &[u8]) -> usize { bytes.len() }
pub fn read(bytes: &[u8], index: usize) -> u8 { bytes[index] }
pub fn write(bytes: &mut [u8], index: usize, value: u8) { bytes[index] = value; }
pub fn alias(bytes: &mut [u8], index: usize) -> u8 { let alias = &mut *bytes; alias[index] }

// Reborrows preserve the same data pointer and full-width metadata across calls.
pub fn write_read(bytes: &mut [u8], index: usize, value: u8) -> u8 {
    let alias = &mut *bytes;
    write(alias, index, value);
    read(alias, index)
}

pub struct Guard<'a> { pub slot: &'a mut i32, pub saved: i32 }
impl Drop for Guard<'_> {
    fn drop(&mut self) { *self.slot = self.saved; }
}
pub fn guarded_read(value: &mut i32, bytes: &[u8], index: usize) -> u32 {
    let saved = *value;
    let guard = Guard { slot: value, saved };
    *guard.slot = 7;
    u32::from(read(bytes, index))
}
