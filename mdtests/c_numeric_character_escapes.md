# Octal, hexadecimal, and simple escapes denote their bytes

An octal escape takes up to three octal digits and a hexadecimal escape takes
every following hexadecimal digit, as in C. Plain `char` is unsigned in the
supported profile, so `'\377'` is 255. In a string literal `"\0012"` is the
byte 1 followed by the character `2`, not a NUL followed by `12`.

```c filename=c_numeric_character_escapes.c
int32 soh(void) {
    return '\001';
}

int32 high(void) {
    return '\377' + '\x7f' + '\0';
}

int32 simple(void) {
    return '\a' + '\b' + '\f' + '\v' + '\?';
}

int32 second_byte(void) {
    const char *text = "\0012\x41";
    return text[0] * 10000 + text[1] * 100 + text[2];
}
```

```click
target "x86_64-linux-kernel";
verifying "c_numeric_character_escapes.c";

int32 soh() {
    ensures result == 1 by auto;
}

int32 high() {
    ensures result == 382 by auto;
}

int32 simple() {
    ensures result == 101 by auto;
}

int32 second_byte() {
    ensures result == 15065 by auto;
}
```

```expect
pass
```
