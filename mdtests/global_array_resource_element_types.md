# Global resource slices retain their C element widths

Byte, halfword, and wide-integer arrays use their declared element type in
resource slices, including unqualified and multidimensional spellings. A
parameter that shadows a global retains its own type.

```c filename=typed_arrays.c
uint8 bytes[2];
uint16 halves[1][2];
uint64 words[2];

uint8 set_byte(uint8 value) {
    bytes[1] = value;
    return bytes[0];
}

uint16 set_half(uint16 value) {
    halves[0][1] = value;
    return halves[0][0];
}

uint64 set_word(uint64 value) {
    words[1] = value;
    return words[0];
}

void set_shadow(int32* bytes) {
    bytes[1] = 7;
}
```

```click
verifying "typed_arrays.c";

uint8 set_byte(uint8 value) {
    views bytes[0..1];
    owns bytes[1..2];
    ensures bytes[1] == value by auto;
    ensures result == old(bytes[0]) by auto;
}

uint16 set_half(uint16 value) {
    views halves[0][0..1];
    owns halves[0][1..2];
    ensures halves[0][1] == value by auto;
    ensures result == old(halves[0][0]) by auto;
}

uint64 set_word(uint64 value) {
    views words[0..1];
    owns words[1..2];
    ensures words[1] == value by auto;
    ensures result == old(words[0]) by auto;
}

void set_shadow(int32* bytes) {
    owns bytes[1..2];
    ensures bytes[1] == 7 by auto;
}
```

```expect
pass
```
