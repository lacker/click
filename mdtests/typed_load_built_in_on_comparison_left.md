# built-in expressions keep their meaning on either comparison side

The typed scalar and pointer loads and `sizeof` are expression primitives, not
user calls. A proposition that starts with one must parse as that expression
regardless of which side of a comparison it starts on, inside arithmetic, or
inside parentheses.

```c filename=typed_load_left.c
uint64 read64(uint64* p) { return *p; }
uint32 read32(uint32* p) { return *p; }
uint8 read8(uint8* p) { return *p; }
int64 readi64(int64* p) { return *p; }
```

```click
verifying "typed_load_left.c";

uint64 read64(uint64* p) {
    views p[0..1];
    ensures load_uint64(p) == result;
} by { step(); simp(); }

uint32 read32(uint32* p) {
    views p[0..1];
    ensures load_uint32(p) == result;
} by { step(); simp(); }

uint8 read8(uint8* p) {
    views p[0..1];
    ensures 1 + load_uint8(p) == result + 1;
} by { step(); simp(); }

int64 readi64(int64* p) {
    views p[0..1];
    ensures (load_int64(p)) == result;
} by { step(); simp(); }

theorem reversed_orientation() {
    ensures 4 == sizeof(int32) by { normalize(); }
}
```

```expect
pass
```
