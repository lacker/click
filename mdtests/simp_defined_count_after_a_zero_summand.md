# simp proves a count's definedness once a zero summand is removed

After `mint_n(o, n)`, the count is the entry count plus `n`, and the entry
count is `0`. `simp` proves `defined(count(tok(o)) + 1)`: it proves
`count(tok(o)) == n` by `simp`, then `defined(n + 1)` from the bounds of
`n`, and rewrites the goal by the first. The same reasoning lets the
implicit `auto` prove the second `mint_n` call's precondition.

```c filename=simp_defined_count_after_a_zero_summand.c
void mint_n(int32* o, int32 n) {}
void increment(int32* o, int32 n) { mint_n(o, n); mint_n(o, 1); }
```

```click
authorized resource tok(o: int32*) {}
verifying "simp_defined_count_after_a_zero_summand.c";
void mint_n(int32* o, int32 n) {
    owns authority(tok(o));
    requires 0 < n;
    requires defined(count(tok(o)) + n);
    produces n of tok(o);
    ensures count(tok(o)) == old(count(tok(o))) + n;
} by { fold(n of tok(o)); execute(); simp(); }
void increment(int32* o, int32 n) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires 0 < n;
    requires n < 2147483647;
    ensures count(tok(o)) == n + 1;
} by { step(); have defined(count(tok(o)) + 1) by simp; execute(); simp(); }
```

```expect
pass
```
