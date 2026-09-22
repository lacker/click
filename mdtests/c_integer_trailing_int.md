# Standard integer width spellings with a trailing int

The typedef retains the exact glibc spelling that blocked the pthread import.
The other functions check signedness, two-byte promotion, casts, and LP64
widths using the same underlying integer types as the shorter spellings.

```c filename=integer_spellings.c
typedef unsigned short int __u_short;
int promote(__u_short value) {
    unsigned short int local = value;
    return (unsigned short int)local;
}
int signed_promote(signed short int value) {
    short int local = value;
    return (signed short int)local;
}
unsigned long long int preserve_wide(unsigned long long int value) {
    return value;
}
int widths(void) {
    return sizeof(short int) + sizeof(unsigned short int)
        + sizeof(long int) + sizeof(unsigned long long int);
}
```

```click
verifying "integer_spellings.c";
int promote(uint16 value) {
    ensures result == value;
} by { execute(); simp(); }
int signed_promote(int16 value) {
    ensures result == value;
} by { execute(); simp(); }
uint64 preserve_wide(uint64 value) {
    ensures result == value;
} by { execute(); simp(); }
int widths() {
    ensures result == 20;
} by { execute(); simp(); }
```

```expect
pass
```
