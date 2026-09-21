# A symbolic population increment overflow

```c filename=population_symbolic_increment_overflow.c
void mint_n(int32* o, int32 n) {}
void increment(int32* o, int32 n) { mint_n(o, n); mint_n(o, 1); }
```

```click
resource tok(o: int32*) {}
verifying "population_symbolic_increment_overflow.c";
void mint_n(int32* o, int32 n) {
    requires 0 < n;
    produces n of tok(o);
} by { execute(); fold(n of tok(o)); simp(); }
void increment(int32* o, int32 n) {
    requires n == 2147483647;
    ensures count(tok(o)) < 0;
} by { execute(); simp(); }
```

```expect
fail: a population count is a nonnegative `int32`
```
