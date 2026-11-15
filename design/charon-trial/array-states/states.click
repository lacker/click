verifying "states.rs";
fn computed_move(a: u32, b: u32) -> u32 {
    ensures result == b ^ 1u32;
}
fn source_write(a: u32, b: u32) -> u32 {
    ensures result == a;
}
fn target_write(a: u32, b: u32) -> u32 {
    ensures result == b;
}
fn replacement(a: u32, b: u32) -> u32 {
    ensures result == b;
}
fn neighbors(a: u32, b: u32) -> u32 {
    ensures result == 28u32;
}
fn sparse(a: u32, b: u32) -> u32 {
    ensures result == b;
}
fn signed(a: i32, b: i32) -> i32 {
    ensures result == b;
}
fn bytes(a: u8, b: u8) -> u8 {
    ensures result == b;
}
