# `strlen` result can drive an explicitly framed byte read

The caller lends `strlen` its borrowed string `cstr_at(bytes, known_len)`,
and the call returns `known_len`. The C code then uses that length as an
array index: the viewed string's bytes are the permission, while its
terminator fact supplies the value read.

```c filename=cstr_dynamic_indexed_read.c
int32 read_terminator(uint8 bytes[], uint64 known_len) {
    uint64 length;
    length = strlen(bytes);
    return bytes[length];
}
```

```click
verifying "cstr_dynamic_indexed_read.c";

int32 read_terminator(uint8 bytes[], uint64 known_len) {
    views click::c::string::cstr_at(bytes, known_len);
    ensures result == '\0';
}
```

```expect
pass
```
