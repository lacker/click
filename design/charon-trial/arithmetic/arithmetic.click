verifying "arithmetic.rs";

uint32 add_byte(uint32 sum, uint8 byte) {
    requires sum <= 4294967040u32;
    ensures result == sum + (uint32)byte;
} by { execute(); simp(); }

uint32 times_three(uint32 value) {
    requires value <= 1431655765u32;
    ensures result == value * 3u32;
} by { execute(); simp(); }

uint32 reduce(uint32 value) {
    ensures result == value % 65521u32;
} by { execute(); simp(); }

uint32 pack(uint32 low, uint32 high) {
    ensures result == ((high << 16) | low);
} by { execute(); simp(); }

uint8 low_byte(uint32 value) {
    ensures ((uint32)result) == (value & 255u32);
} by { execute(); simp(); }

bool high_bit(uint32 value) {
    ensures result == (if value > 2147483647u32 { 1 } else { 0 });
} by {
    if value > 2147483647u32 { execute(); simp(); }
    else { execute(); simp(); }
}

uint8 shifted_byte(uint8 value, uint32 count) {
    requires count < 8u32;
    ensures ((uint32)result) == (((uint32)value << count) & 255u32);
} by { execute(); simp(); }

uint8 discarded_shift_bits() {
    ensures result == 0;
} by { execute(); simp(); }

uint8 quotient_byte(uint8 value, uint8 divisor) {
    requires divisor != 0;
    ensures ((uint32)result) == (uint32)value / (uint32)divisor;
} by { execute(); simp(); }
uint16 quotient_word(uint16 value, uint16 divisor) {
    requires divisor != 0;
    ensures ((uint32)result) == (uint32)value / (uint32)divisor;
} by { execute(); simp(); }
uint32 quotient(uint32 value, uint32 divisor) {
    requires divisor != 0u32;
    ensures result == value / divisor;
} by { execute(); simp(); }
uint16 remainder_word(uint16 value, uint16 divisor) {
    requires divisor != 0;
    ensures ((uint32)result) == (uint32)value % (uint32)divisor;
} by { execute(); simp(); }
uint64 wide_quotient(uint64 value, uint64 divisor) {
    requires divisor != 0u64;
    ensures result == value / divisor;
} by { execute(); simp(); }
uint64 wide_remainder(uint64 value, uint64 divisor) {
    requires divisor != 0u64;
    ensures result == value % divisor;
} by { execute(); simp(); }
uint64 wide_left(uint64 value, uint64 count) {
    requires count < 64u64;
    ensures result == value << count;
} by { execute(); simp(); }
uint64 wide_right(uint64 value, uint64 count) {
    requires count < 64u64;
    ensures result == value >> count;
} by { execute(); simp(); }
uint16 word_right(uint16 value, uint64 count) {
    requires count < 16u64;
    ensures ((uint32)result) == (((uint32)value >> count) & 65535u32);
} by { execute(); simp(); }
uint32 signed_count(uint32 value, int32 count) {
    requires 0 <= count and count < 32;
    ensures result == value << count;
} by { execute(); simp(); }
uint8 invert_byte(uint8 value) { ensures ((uint32)result) == ((~(uint32)value) & 255u32); } by { execute(); simp(); }
uint16 invert_word(uint16 value) { ensures ((uint32)result) == ((~(uint32)value) & 65535u32); } by { execute(); simp(); }
uint32 invert(uint32 value) { ensures result == ~value; } by { execute(); simp(); }
uint64 wide_invert(uint64 value) { ensures result == ~value; } by { execute(); simp(); }
uint32 masked(uint32 value, uint32 mask) { ensures result == ((value & mask) ^ ~value); } by { execute(); simp(); }
uint32 conditional_divide(uint32 value, uint32 divisor, bool skip) {
    requires skip != 0 or divisor != 0u32;
    ensures skip != 0 implies result == 0u32;
    ensures skip == 0 implies result == value / divisor;
} by { if skip != 0 { execute(); simp(); } else { have divisor != 0u32 by { cases(skip != 0 or divisor != 0u32) { contradiction(skip != 0); } { assumption(); } } execute(); simp(); } }
