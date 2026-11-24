# A symbolic call refuses an unwritten byte source

Ownership of the full range supplies storage. The call also requires a
checked proof that the range's bytes are initialized.

```c filename=source.c
unsigned long inspect(const unsigned char* bytes, unsigned long n) {
    return n;
}

unsigned long probe(unsigned char* bytes, unsigned long n) {
    return inspect(bytes, n);
}
```

```click
verifying "source.c";

uint64 inspect(const uint8* bytes, uint64 n) {
    views bytes[0..n];
    ensures result == n;
}

uint64 probe(uint8* bytes, uint64 n) {
    owns uninitialized(bytes[0..n]);
    requires n > 0u64;
    ensures result == n;
} by {
    step() by { close(); }
}
```

```expect
fail: could not establish `forall
```
