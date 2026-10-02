pub fn add_byte(sum: u32, byte: u8) -> u32 {
    sum + byte as u32
}

pub fn times_three(value: u32) -> u32 {
    value * 3
}

pub fn reduce(value: u32) -> u32 {
    value % 65521
}

pub fn pack(low: u32, high: u32) -> u32 {
    (high << 16) | low
}

pub fn low_byte(value: u32) -> u8 {
    value as u8
}

pub fn high_bit(value: u32) -> bool {
    value > 2147483647
}

pub fn shifted_byte(value: u8, count: u32) -> u8 {
    value << count
}

pub fn discarded_shift_bits() -> u8 {
    128u8 << 1
}

pub fn quotient_byte(value: u8, divisor: u8) -> u8 { value / divisor }
pub fn quotient_word(value: u16, divisor: u16) -> u16 { value / divisor }
pub fn quotient(value: u32, divisor: u32) -> u32 { value / divisor }
pub fn remainder_word(value: u16, divisor: u16) -> u16 { value % divisor }
pub fn wide_quotient(value: usize, divisor: usize) -> usize { value / divisor }
pub fn wide_remainder(value: usize, divisor: usize) -> usize { value % divisor }
pub fn wide_left(value: usize, count: usize) -> usize { value << count }
pub fn wide_right(value: usize, count: usize) -> usize { value >> count }
pub fn word_right(value: u16, count: usize) -> u16 { value >> count }
pub fn signed_count(value: u32, count: i32) -> u32 { value << count }
pub fn invert_byte(value: u8) -> u8 { !value }
pub fn invert_word(value: u16) -> u16 { !value }
pub fn invert(value: u32) -> u32 { !value }
pub fn wide_invert(value: usize) -> usize { !value }
pub fn masked(value: u32, mask: u32) -> u32 { (value & mask) ^ !value }
pub fn conditional_divide(value: u32, divisor: u32, skip: bool) -> u32 {
    if skip { 0 } else { value / divisor }
}
