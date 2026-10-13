# A mixed-index pointer borrows through its checked absolute position

```c filename=mixed.c
unsigned char first(const unsigned char *p) { return p[0]; }
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index, unsigned long prefix, int pos) { return first((bytes + prefix) + pos); }
```

```click
verifying "mixed.c";
uint8 first(const uint8* p) {
 views p[0u64..4u64];
 ensures result == old(p[0]);
} by { execute(); simp(); }
uint8 read(const uint8* bytes, uint64 length, uint64 index, uint64 prefix, int32 pos) {
 views bytes[0u64..length];
 requires length <= 2147483647u64;
 requires index <= length;
 requires prefix <= length;
 requires 0 <= pos;
 requires (uint64)(uint32)pos <= length - prefix;
 requires 4u64 <= length - index;
 requires (bytes + prefix) + pos == bytes + index;
 ensures result == old(((bytes + prefix) + pos)[0]);
} by { execute(); simp(); }
```

```expect
pass
```
