# Repeated births require a checked non-wrapping total

The same C is retained, but the contract omits the definedness condition
needed to prove the second count addition safe.

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
void run(int32* o, int32 n, int32 m) {
    owns authority(tok(o));
    requires count(tok(o)) == 0;
    requires 0 < n;
    requires 0 < m;
    produces (n + m) of tok(o);
    ensures count(tok(o)) == n + m;
}
```

```expect
fail: `have` failed
```
