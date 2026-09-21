# A symbolic population increment bounded

```c filename=population_symbolic_increment_bounded.c
void mint_n(int32* o, int32 n) {}
void increment(int32* o, int32 n) { mint_n(o, n); mint_n(o, 1); }
```

```click
resource tok(o: int32*) {}
verifying "population_symbolic_increment_bounded.c";
void mint_n(int32* o, int32 n) {
    requires 0 < n;
    produces n of tok(o);
} by { execute(); fold(n of tok(o)); simp(); }
void increment(int32* o, int32 n) {
    requires 0 < n;
    requires n < 2147483647;
    ensures count(tok(o)) == n + 1;
} by { execute(); simp(); }
```

```expect
pass
```
