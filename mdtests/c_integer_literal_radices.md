# C integer literal radices and suffixes

Hexadecimal and octal constants retain their ordinary C meaning, while
standard integer suffixes remain harmless for the modeled `int32` values.

```c filename=literal_mask.c
int32 literal_mask() {
    return (0x0FU | 010UL) & 0x0FLL;
}
```

```click
verifying "literal_mask.c";

int32 literal_mask() {
    ensures result == 15;
}
```

```expect
pass
```
