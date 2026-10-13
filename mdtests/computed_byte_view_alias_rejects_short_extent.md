# A computed byte-view alias cannot borrow beyond its checked extent

```c filename=alias.c
unsigned char first(const unsigned char *p) { return p[0]; }
unsigned char read(const unsigned char *bytes, const unsigned char *base, unsigned long length, unsigned long index, int pos) { return first(base + pos); }
```

```click
verifying "alias.c";
uint8 first(const uint8* p) {
 views p[0..4];
 ensures result == old(p[0]);
} by { execute(); simp(); }
uint8 read(const uint8* bytes, const uint8* base, uint64 length, uint64 index, int32 pos) {
 views bytes[0..length];
 requires index <= length;
 requires length - index == 3u64;
 requires base + pos == bytes + index;
 ensures result == old((base + pos)[0]);
} by { execute(); simp(); }
```

```expect
fail: stable-view
```
