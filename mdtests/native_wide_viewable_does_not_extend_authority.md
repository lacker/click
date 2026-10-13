# Native wide viewable does not extend authority

```c filename=native_wide_viewable_does_not_extend_authority.c
void hold(const unsigned char *bytes, unsigned long length) {}
```

```click
verifying "native_wide_viewable_does_not_extend_authority.c";
void hold(const uint8* bytes, uint64 length) {
 requires length < 2147483647u64;
 views bytes[0..length];
} by {
 have viewable(bytes[0u64..length + 1u64]);
 execute(); simp();
}
```

```expect
fail: kernel native view checker did not establish
```
