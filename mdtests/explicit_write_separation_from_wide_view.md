# A write proves a wide-view separation obligation explicitly

The driver must retain the explicit separation proof. The viewed resources
supply their own validity premises; separation adds no span obligations.

```c filename=a_separation_from_a_64_bit_range.c
unsigned char set_and_read(int *value, const unsigned char *bytes, unsigned long length, unsigned long index) {
    *value = 7;
    return bytes[index];
}
```

```click
verifying "a_separation_from_a_64_bit_range.c";
uint8 set_and_read(int32* value, const uint8* bytes, uint64 length, uint64 index) {
    requires index < length;
    requires separate(memory(value[0..1]), memory(bytes[0..length]));
    owns value[0..1];
    views bytes[0..length];
    ensures result == old(bytes[index]);
    ensures value[0] == 7;
} by {
        have separate(memory(value[0..1]), memory(bytes[0..length])) by { close(); }
        step() by { close(); }
}
```

```expect
pass
```
