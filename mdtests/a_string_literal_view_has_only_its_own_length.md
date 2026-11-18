# A string literal's view has only its own length

The literal `"kB"` is the C string of length 2. A contract that views it as
`cstr_at(p, 1u64)` names a length its bytes do not have: byte 1 is `B`, not
the terminator, so the view is refused, naming the body fact that fails.

```c filename=wrong_length.c
int take(const char *p);

int direct(void)
{
	return take("kB");
}
```

```click
verifying "wrong_length.c";

extern int32 take(const uint8* p) {
    views click::c::string::cstr_at(p, 1u64);
    ensures true;
}

int32 direct() {
    ensures true;
}
```

```expect
fail: `p[len] == 0u8`
```
