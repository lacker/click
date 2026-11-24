# Combined symbolic births cannot certify just the first quantity

The same C and batch custody are retained. The false claim that the resulting
population equals only the first positive quantity must be rejected.

After the second creation, the earlier fact that the count was `n` is stale.
Check that exact fact explicitly so this negative test does not spend the
smart-search budget trying to prove a false total.

```c filename=symbolic_birth_composition.c
void mint_pair(int32* o, int32 n, int32 m) {}
void run(int32* o, int32 n, int32 m) { mint_pair(o, n, m); }
```

```click
authorized resource tok(o: int32*) {}
verifying "symbolic_birth_composition.c";
void mint_pair(int32* o, int32 n, int32 m) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires 0 < n;
    requires 0 < m;
    requires defined(n + m);
    requires 0 <= n + m;
    produces (n + m) of tok(o);
    ensures count(tok(o)) == n;
} by {
    fold(n of tok(o));
    have count(tok(o)) == n by close();
    have defined(count(tok(o)) + m) by {
        rewrite(count(tok(o)), n);
        close();
    }
    fold(m of tok(o));
    have count(tok(o)) == n by close();
}
void run(int32* o, int32 n, int32 m) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires 0 < n;
    requires 0 < m;
    requires defined(n + m);
    requires 0 <= n + m;
    produces (n + m) of tok(o);
    ensures count(tok(o)) == n;
}
```

```expect
fail: could not establish `to_integer(count(tok(o))) == to_integer(n)`
```
