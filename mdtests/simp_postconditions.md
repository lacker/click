# simp proves local postcondition normalization

This checks the conservative `simp` tactic. It proves straight-line
postconditions by deterministic local normalization, not by loop verification or
effect reasoning.

```c filename=simp_postconditions.c
int32 simp_postconditions(int32 x) {
    return x;
}
```

```click
verifying "simp_postconditions.c";

int32 simp_postconditions(int32 x) {
    ensures add_zero: result == x + 0 by simp;
    ensures prop_simp: result == x and not (result != x) by simp;
}
```

```expect
pass
```
