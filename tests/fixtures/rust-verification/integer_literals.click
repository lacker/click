verifying "literals.rs";

theorem literal_forms(word: u16, index: usize, signed_word: i32) {
    requires word == 0xff_ff;
    requires index == 0b1_010;
    requires signed_word == -0x8000_0000;
    ensures word == 65_535u16 by { close(); }
    ensures index == 0o12usize by { close(); }
    ensures signed_word == -2_147_483_648i32 by { close(); }
}
