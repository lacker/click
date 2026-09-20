# separate proves a symbolic unwritten read

This checks that `requires separate(memory(...), memory(...))` is consumed by framing. The
function writes `p[i]` and reads `p[j]`; the postcondition follows because the
two singleton ranges are declared separate.

The contract now says it twice. `consumes p[i..i + 1]` is transferred and
`views p[j..j + 1]` is borrowed, and a contract's transferred and borrowed
clauses denote disjoint memory
(`docs/internals/resource-tracker.md`, "The entry partition"), so the two
indexes are apart whether or not the `separate(...)` is written — a caller
passing `i == j` is refused at the call rather than here. The written clause
stays, because what this fixture checks is that it is *consumed by framing*
and survives expansion. The check that a stated separation is load-bearing
where nothing implies it is
`a_stated_separation_is_load_bearing`
(`src/surface/tests/expansion_tests.rs`), over
`a_separated_array_argument_survives_a_global_store.md`.

```c filename=write_i_read_j.c
int32 write_i_read_j(int32 p[], int32 i, int32 j, int32 n) {
    p[i] = 9;
    return p[j];
}
```

```click
verifying "write_i_read_j.c";

int32 write_i_read_j(int32 p[], int32 i, int32 j, int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires i >= 0;
    requires i < n;
    requires j >= 0;
    requires j < n;
    consumes p[i..i + 1];
    views p[j..j + 1];
    requires separate(memory(p[i..i + 1]), memory(p[j..j + 1]));
    ensures keeps_j: result == old(p[j]) by auto;
}
```

```expect
pass
```
