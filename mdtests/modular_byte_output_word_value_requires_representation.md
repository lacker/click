# Modular byte output determines the declared uint32 word

Initialization establishes readable storage independently of byte values.
The shared representation rule projects the four byte postconditions from one
initialized declared uint32 observation under the selected little-endian target.
Those exact bytes determine the unchanged word-value claim. Smart simplification
expands to an explicit application retaining all four snapshot-relative premises.

```c filename=output.c
void fill(unsigned char* p) {
    p[0] = 120;
    p[1] = 86;
    p[2] = 52;
    p[3] = 18;
}
unsigned char first(void) {
    unsigned int obj;
    unsigned char* bytes = (unsigned char*)(void*)&obj;
    fill(bytes);
    return bytes[0];
}
unsigned int word(void) {
    unsigned int obj;
    unsigned char* bytes = (unsigned char*)(void*)&obj;
    fill(bytes);
    return obj;
}
```

```click
verifying "output.c";
void fill(uint8* p) {
    owns p[0..4];
    ensures initialized(p[0..4]);
    ensures p[0] == 120u8;
    ensures p[1] == 86u8;
    ensures p[2] == 52u8;
    ensures p[3] == 18u8;
} by { execute(); simp(); }
uint8 first() { ensures result == 120u8; } by { execute(); simp(); }
uint32 word() { ensures result == 305419896u32; } by { execute(); simp(); }
```

```expect
pass
```
