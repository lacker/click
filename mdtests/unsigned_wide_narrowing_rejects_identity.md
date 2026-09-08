# Truncation cannot prove that a wide input is preserved

```c filename=narrow.c
unsigned int narrow(unsigned long x) { return x; }
```

```click
verifying "narrow.c";
unsigned int narrow(unsigned long x) {
    ensures result == x;
} by { execute(); simp(); }
```

```expect
fail: unclosed goal
```
