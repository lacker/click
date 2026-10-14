# Native byte reads retain their checked index beside a narrow alias

An equivalent int32 pointer spelling must not displace the native index
whose full-width bounds authorize the pre-increment byte read. Equality
selects a held view; it cannot supply one.
```c filename=read.c
int read(const unsigned char *cursor, const unsigned char *base, unsigned long held, unsigned long remaining, const unsigned char *alternate, int narrow) { return *cursor++; }
```
```click
target "x86_64-linux-userspace";
verifying "read.c";
int32 read(const uint8* cursor, const uint8* base, uint64 held, uint64 remaining, const uint8* alternate, int32 narrow) {
 requires 1u64 <= remaining;
 requires remaining <= held;
 requires held <= 15u64;
 requires cursor == alternate + narrow;
 requires cursor == base + (held - remaining);
 views base[0u64..held];
 ensures 0 <= result and result <= 255;
} by {
 have held - remaining < held by arithmetic() using { 1u64 <= remaining; remaining <= held; held <= 15u64; };
 have held <= 9223372036854775807u64 by arithmetic() using { held <= 15u64; };
 execute(); simp();
}
```
```expect
pass
```
