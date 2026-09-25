# Logical reads are total and can be named under a binder

Neither a reflexive equality nor an existential witness performs a C memory
access. No range or permission is required to state these logical values.

```click
theorem arbitrary_cell(p: int32[]) {
    ensures p[0] == p[0] by { simp(); }
    ensures exists (k: Integer) { p[to_int32(k)] == p[to_int32(k)] } by {
        witness(k = 0);
        simp();
    }
}
```

```expect
pass
```
