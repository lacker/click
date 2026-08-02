# C bitwise operators

This checks C0 bitwise operators on `int32` values, Surface Click
postconditions using the same operators, C-style precedence, and `uint8`
integer promotion through bitwise expressions.

```c filename=bitwise_mask.c
int32 bitwise_mask(int32 x) {
    return x & 15;
}
```

```c filename=bitwise_precedence.c
int32 bitwise_precedence() {
    return 1 | 2 & 0;
}
```

```c filename=bitwise_constant.c
int32 bitwise_constant() {
    return 42 & 15;
}
```

```c filename=bitwise_xor_or.c
int32 bitwise_xor_or() {
    return 8 | 2 ^ 1;
}
```

```c filename=bitwise_not.c
int32 bitwise_not_zero() {
    return ~0;
}
```

```c filename=bitwise_uint8_promoted.c
int32 bitwise_uint8_promoted(uint8 x) {
    return x & 15;
}
```

```c filename=bitwise_uint8_not.c
int32 bitwise_uint8_not(uint8 x) {
    return ~x;
}
```

```c filename=bitwise_uint8_narrow_constant.c
uint8 bitwise_uint8_narrow_constant() {
    return 42 & 15;
}
```

```click
verifying "bitwise_mask.c";
verifying "bitwise_precedence.c";
verifying "bitwise_constant.c";
verifying "bitwise_xor_or.c";
verifying "bitwise_not.c";
verifying "bitwise_uint8_promoted.c";
verifying "bitwise_uint8_not.c";
verifying "bitwise_uint8_narrow_constant.c";

function low_nibble(x: int32) -> int32 {
    x & 15
}

function byte_low_nibble(x: uint8) -> int32 {
    x & 15
}

function all_bits() -> int32 {
    ~0
}

function byte_not(x: uint8) -> int32 {
    ~x
}

int32 bitwise_mask(int32 x) {
    requires x == 42;
    ensures symbolic_mask: result == low_nibble(x) by auto;
}

int32 bitwise_precedence() {
    ensures precedence: result == 1 by auto;
}

int32 bitwise_constant() {
    ensures concrete_mask: result == 10 by auto;
}

int32 bitwise_xor_or() {
    ensures xor_before_or: result == 11 by auto;
}

int32 bitwise_not_zero() {
    ensures surface_not: result == all_bits() by auto;
    ensures concrete_not: result == 4294967295 by auto;
}

int32 bitwise_uint8_promoted(uint8 x) {
    ensures promoted_byte_mask: result == byte_low_nibble(x) by auto;
}

int32 bitwise_uint8_not(uint8 x) {
    ensures promoted_byte_not: result == byte_not(x) by auto;
}

uint8 bitwise_uint8_narrow_constant() {
    ensures narrowed_constant: result == 10 by auto;
}
```

```expect
pass
```
