# A consuming helper cannot split a symbolic batch

The quantities remain symbolic. One helper returns a complete coalesced batch;
a second helper consumes that entire batch through the checked call engine.
The caller regains authority over an empty population.

```c filename=symbolic_batch_retirement.c
void mint_pair(int32* o, int32 n, int32 m) {}
void spend_n(int32* o, int32 n) {}
void run(int32* o, int32 n, int32 m) { mint_pair(o, n, m); spend_n(o, n); }
```

```click
authorized resource tok(o: int32*) {}
verifying "symbolic_batch_retirement.c";
void mint_pair(int32* o, int32 n, int32 m) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires 0 < n;
    requires 0 < m;
    requires defined(n + m);
    requires 0 <= to_integer(n + m);
    produces (n + m) of tok(o);
    ensures count(tok(o)) == n + m;
} by {
    fold(n of tok(o));
    have count(tok(o)) == n by close();
    have defined(count(tok(o)) + m) by {
        rewrite(count(tok(o)), n);
        close();
    }
    fold(m of tok(o));
}
void spend_n(int32* o, int32 n) {
    owns authority(tok(o));
    requires 0 <= n;
    consumes n of tok(o);
    ensures count(tok(o)) == old(count(tok(o))) - n;
} by { unfold(n of tok(o)); }
void run(int32* o, int32 n, int32 m) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires 0 < n;
    requires 0 < m;
    requires defined(n + m);
    requires 0 <= to_integer(n + m);
    ensures count(tok(o)) == 0;
}
```

```expect
fail: population call transfer refused
```
