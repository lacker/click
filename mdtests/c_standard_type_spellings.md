# standard C integer spellings map to the modeled types

The imported C source may use the ordinary spellings for the integer types
that Click already models. The sidecar accepts the same spellings.

```c filename=c_standard_type_spellings.c
int standard_types(int p[], unsigned char byte, int32_t index, uint8_t tag) {
    int result;
    uint8_t local_tag;
    result = p[index];
    local_tag = tag;
    return result + byte + local_tag;
}
```

```click
verifying "c_standard_type_spellings.c";

int standard_types(int p[], unsigned char byte, int32_t index, uint8_t tag) {
    requires 0 <= index;
    requires index < 3;
    requires p[index] <= 2147483137;
    requires loadable(p[0..3]);
    views p[0..3];
    immutable;
    ensures result == p[index] + byte + tag by auto;
}
```

```expect
pass
```
