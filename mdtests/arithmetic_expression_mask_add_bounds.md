# Signed addition uses the exact Integer bounds of a masked word

```c filename=arithmetic.c
int64 with_word_facts(int64 n, int64 k) { return n + (k & 15LL); }
int64 implicit(int64 n, int64 k) { return n + (k & 15LL); }
```

```click
verifying "arithmetic.c";

int64 with_word_facts(int64 n, int64 k) {
    requires n <= 9223372036854775792i64;
    ensures true;
} by {
    step() by {
        have (k & 15i64) >= 0 by { close(); }
        have (k & 15i64) <= 15 by { close(); }
        close();
    }
}
int64 implicit(int64 n, int64 k) {
    requires n <= 9223372036854775792i64;
    ensures true;
}
```

```expect
pass
```
