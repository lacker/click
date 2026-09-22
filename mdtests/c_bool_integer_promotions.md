# Boolean integer promotions in C operators

Both boolean values promote to `int32` when used with ordinary scalar
operators. The operands below exercise both positions and signed, unsigned,
and wide partners.

```c filename=boolean.c
#include <stdbool.h>

int add_bool_left(void) { _Bool b = 1; return b + 1; }
int add_bool_right(void) { bool b = 0; return 2 + b; }
int subtract_bool_left(void) { _Bool b = 1; return b - 1; }
int subtract_bool_right(void) { _Bool b = 1; return 3 - b; }
int multiply_bool(void) { _Bool b = 1; return b * 3; }
int divide_bool(void) { _Bool b = 1; return 4 / b; }
int remainder_bool(void) { _Bool b = 1; return 4 % b; }
int compare_bool_left(void) { _Bool b = 1; return b < 2; }
int compare_bool_right(void) { _Bool b = 0; return 2 > b; }
int equal_bool(void) { _Bool b = 1; return b == 1; }
int not_equal_bool(void) { _Bool b = 0; return 1 != b; }
int bitwise_bool(void) { _Bool b = 1; return (b & 3) | (2 ^ b); }
int bitwise_not_bool(void) { _Bool b = 1; return ~b; }
unsigned int unsigned_bool(void) { _Bool b = 1; return b + 2u; }
long wide_bool(void) { _Bool b = 1; return b + 2L; }
int shift_bool(void) { _Bool b = 1; return b << 1; }
```

```click
verifying "boolean.c";

int32 add_bool_left() { ensures result == 2; } by { execute(); simp(); }
int32 add_bool_right() { ensures result == 2; } by { execute(); simp(); }
int32 subtract_bool_left() { ensures result == 0; } by { execute(); simp(); }
int32 subtract_bool_right() { ensures result == 2; } by { execute(); simp(); }
int32 multiply_bool() { ensures result == 3; } by { execute(); simp(); }
int32 divide_bool() { ensures result == 4; } by { execute(); simp(); }
int32 remainder_bool() { ensures result == 0; } by { execute(); simp(); }
int32 compare_bool_left() { ensures result == 1; } by { execute(); simp(); }
int32 compare_bool_right() { ensures result == 1; } by { execute(); simp(); }
int32 equal_bool() { ensures result == 1; } by { execute(); simp(); }
int32 not_equal_bool() { ensures result == 1; } by { execute(); simp(); }
int32 bitwise_bool() { ensures result == 3; } by { execute(); simp(); }
int32 bitwise_not_bool() { ensures result == -2; } by { execute(); simp(); }
uint32 unsigned_bool() { ensures result == 3; } by { execute(); simp(); }
int64 wide_bool() { ensures result == 3; } by { execute(); simp(); }
int32 shift_bool() { ensures result == 2; } by { execute(); simp(); }
```

```expect
pass
```
