verifying "owned.rs";
fn construct(value: u32, index: usize) -> u32 {
    requires index < 4u64;
    ensures result == value;
}
fn moved(value: u32, index: usize) -> u32 {
    requires index < 4u64;
    ensures result == value;
}
fn reassigned(value: u32, replacement: u32) -> u32 {
    ensures result == replacement;
}
fn neighboring_fields(value: u32, replacement: u32) -> u32 {
    ensures result == 28u32;
}
fn extracted(value: u32, index: usize) -> u32 {
    requires index < 4u64;
    ensures result == value;
}
fn copied_value(value: u32) -> u32 {
    ensures result == value;
}
fn tuple_move(value: u32) -> u32 {
    ensures result == value;
}
fn byte_move(value: u8) -> u8 {
    ensures result == value;
}
fn empty_move(value: u8) -> u8 {
    ensures result == 31u8;
}
