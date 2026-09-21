# A contract cannot own and view overlapping offset aliases

The store writes `p[1]`. The claimed result was previously obtained by treating
the owned and viewed clauses as separate despite the pointer equality.

```c filename=contract_view_offset_alias.c
int32 aliased(int32* p, int32* w) { int32 t; w[0] = 7; t = p[1]; return t; }
```

```click
verifying "contract_view_offset_alias.c";
int32 aliased(int32* p, int32* w) {
    requires w == p + 1;
    requires p[1] == 3;
    views p[0..3];
    consumes w[0..3];
    ensures result == 3;
} by { execute(); simp(); }
```

```expect
fail: the contract's `views` clause overlaps its own `owns` clause
```
