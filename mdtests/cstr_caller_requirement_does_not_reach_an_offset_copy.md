# A caller's C-string requirement does not reach a copy that points elsewhere

`p = bytes + 1` is not the pointer of the caller's string
`cstr_at(bytes, n)`, so `strlen(p)` finds no string at `p` to view.

```c filename=cstr_offset_copy.c
uint64 offset(uint8 bytes[]) {
    uint8* p;
    p = bytes + 1;
    return strlen(p);
}
```

```click
verifying "cstr_offset_copy.c";

uint64 offset(uint8 bytes[]) {
    let n: uint64;
    views click::c::string::cstr_at(bytes, n);
    ensures result == result;
}
```

```expect
fail: call to `strlen` needs a held `cstr_at` instance to give `n` its value
```
