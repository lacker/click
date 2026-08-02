# separate proves a symbolic unwritten read

This checks that `requires separate(memory(...), memory(...))` is consumed by effect reasoning. The
function writes `p[i]` and reads `p[j]`; the postcondition follows because the
two singleton ranges are declared separate.

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
    requires loadable(p[0..n]);
    consumes p[i..i + 1];
    views p[j..j + 1];
    requires separate(memory(p[i..i + 1]), memory(p[j..j + 1]));
    mutable p[i..i + 1] by auto;
    ensures keeps_j: result == old(p[j]) by auto;
}
```

```expect
pass
```
